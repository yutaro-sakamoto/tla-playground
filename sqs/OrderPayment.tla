--------------------------- MODULE OrderPayment ---------------------------
(***************************************************************************)
(* 例: orders キュー -> OrderFn -> payments キュー -> PaymentFn            *)
(*                                                                         *)
(* ユーザーが書くのは (U) の部分だけ。(L) はライブラリ提供の雛形で、       *)
(* PlusCal にはモジュール分割の仕組みがないため、そのまま貼り付けて使う。   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Idempotent   \* TRUE: 冪等な決済 / FALSE: 素朴な決済(バグ版)

\* ==== (U) トポロジ定義 ====================================================
Orders  == {"o1"}
Trigger == [OrderFn |-> "orders", PaymentFn |-> "payments"]   \* 関数 -> 起動キュー
Workers == [w \in {"order-1", "pay-1", "pay-2"} |->            \* 同時実行インスタンス
              IF w = "order-1" THEN "OrderFn" ELSE "PaymentFn"]

SQS == INSTANCE SqsLib WITH
         Redrive    <- [orders |-> "orders-dlq", payments |-> "payments-dlq"],
         MaxReceive <- 2

(* --algorithm OrderPayment

variables
    \* (L) キュー全体の状態。初期メッセージだけユーザーが指定
    sqs = SQS!SendSet(SQS!Empty, "orders", Orders),

    \* (U) 業務状態
    db      = {},                         \* 受注済み
    charged = [o \in Orders |-> 0],       \* 課金回数
    paid    = {};                         \* 冪等キー

\* ==== (U) 業務ロジック ======================================================
\* fn と body を受け取り、業務変数を更新し、送信したいメッセージを out に入れる
macro Handler(fn, body) begin
    if fn = "OrderFn" then
        db  := db \cup {body};
        out := << [q |-> "payments", body |-> body] >>;
    elsif fn = "PaymentFn" then
        if Idempotent /\ body \in paid then
            skip;                                   \* 課金済みなら何もしない
        else
            charged[body] := charged[body] + 1;
            paid := paid \cup {body};
        end if;
    end if;
end macro;

\* ==== (L) ライブラリ雛形: Lambda 実行のライフサイクル =========================
\* 受信 -> 業務処理 -> 送信 -> 削除。各段階の間でクラッシュしうる
fair process Lambda \in DOMAIN Workers
variables h = SQS!NoHandle, out = << >>;
begin
L_Recv:
    with id \in SQS!Receivable(sqs, Trigger[Workers[self]]) do
        sqs := SQS!Receive(sqs, id);
        h   := SQS!HandleOf(sqs, id);
    end with;
L_Exec:
    either
        Handler(Workers[self], h.body);   \* 業務処理成功
    or
        goto L_Recv;                       \* 例外 / 処理前にクラッシュ
    end either;
L_Send:
    either
        sqs := SQS!SendAll(sqs, out);
    or
        out := << >>;                      \* 業務処理後・送信前にクラッシュ
        goto L_Recv;
    end either;
L_Delete:
    either
        sqs := SQS!Delete(sqs, h);
    or
        skip;                              \* 削除前にクラッシュ
    end either;
    out := << >>;
    goto L_Recv;
end process;

\* ==== (L) ライブラリ雛形: 可視性タイムアウトと DLQ 移動 =======================
fair process Infra = "sqs-infra"
begin
I_Step:
    while TRUE do
        with s \in SQS!InfraNext(sqs) do
            sqs := s;
        end with;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES pc, sqs, db, charged, paid, h, out

vars == << pc, sqs, db, charged, paid, h, out >>

ProcSet == (DOMAIN Workers) \cup {"sqs-infra"}

Init == (* Global variables *)
        /\ sqs = SQS!SendSet(SQS!Empty, "orders", Orders)
        /\ db = {}
        /\ charged = [o \in Orders |-> 0]
        /\ paid = {}
        (* Process Lambda *)
        /\ h = [self \in DOMAIN Workers |-> SQS!NoHandle]
        /\ out = [self \in DOMAIN Workers |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in DOMAIN Workers -> "L_Recv"
                                        [] self = "sqs-infra" -> "I_Step"]

L_Recv(self) == /\ pc[self] = "L_Recv"
                /\ \E id \in SQS!Receivable(sqs, Trigger[Workers[self]]):
                     /\ sqs' = SQS!Receive(sqs, id)
                     /\ h' = [h EXCEPT ![self] = SQS!HandleOf(sqs', id)]
                /\ pc' = [pc EXCEPT ![self] = "L_Exec"]
                /\ UNCHANGED << db, charged, paid, out >>

L_Exec(self) == /\ pc[self] = "L_Exec"
                /\ \/ /\ IF (Workers[self]) = "OrderFn"
                            THEN /\ db' = (db \cup {(h[self].body)})
                                 /\ out' = [out EXCEPT ![self] = << [q |-> "payments", body |-> (h[self].body)] >>]
                                 /\ UNCHANGED << charged, paid >>
                            ELSE /\ IF (Workers[self]) = "PaymentFn"
                                       THEN /\ IF Idempotent /\ (h[self].body) \in paid
                                                  THEN /\ TRUE
                                                       /\ UNCHANGED << charged, 
                                                                       paid >>
                                                  ELSE /\ charged' = [charged EXCEPT ![(h[self].body)] = charged[(h[self].body)] + 1]
                                                       /\ paid' = (paid \cup {(h[self].body)})
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << charged, paid >>
                                 /\ UNCHANGED << db, out >>
                      /\ pc' = [pc EXCEPT ![self] = "L_Send"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "L_Recv"]
                      /\ UNCHANGED <<db, charged, paid, out>>
                /\ UNCHANGED << sqs, h >>

L_Send(self) == /\ pc[self] = "L_Send"
                /\ \/ /\ sqs' = SQS!SendAll(sqs, out[self])
                      /\ pc' = [pc EXCEPT ![self] = "L_Delete"]
                      /\ out' = out
                   \/ /\ out' = [out EXCEPT ![self] = << >>]
                      /\ pc' = [pc EXCEPT ![self] = "L_Recv"]
                      /\ sqs' = sqs
                /\ UNCHANGED << db, charged, paid, h >>

L_Delete(self) == /\ pc[self] = "L_Delete"
                  /\ \/ /\ sqs' = SQS!Delete(sqs, h[self])
                     \/ /\ TRUE
                        /\ sqs' = sqs
                  /\ out' = [out EXCEPT ![self] = << >>]
                  /\ pc' = [pc EXCEPT ![self] = "L_Recv"]
                  /\ UNCHANGED << db, charged, paid, h >>

Lambda(self) == L_Recv(self) \/ L_Exec(self) \/ L_Send(self)
                   \/ L_Delete(self)

I_Step == /\ pc["sqs-infra"] = "I_Step"
          /\ \E s \in SQS!InfraNext(sqs):
               sqs' = s
          /\ pc' = [pc EXCEPT !["sqs-infra"] = "I_Step"]
          /\ UNCHANGED << db, charged, paid, h, out >>

Infra == I_Step

Next == Infra
           \/ (\E self \in DOMAIN Workers: Lambda(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in DOMAIN Workers : WF_vars(Lambda(self))
        /\ WF_vars(Infra)

\* END TRANSLATION

\* ==== (U) 検証したい性質 ====================================================
\* 二重課金しない
NoDoubleCharge == \A o \in Orders : charged[o] <= 1

\* 最終的にソースキューは空になり、各注文は課金済みか DLQ に入っている
Settled ==
    /\ SQS!Drained(sqs, {"orders", "payments"})
    /\ \A o \in Orders :
         \/ charged[o] >= 1
         \/ o \in SQS!BodiesIn(sqs, "orders-dlq") \cup SQS!BodiesIn(sqs, "payments-dlq")

EventuallySettled == <>[]Settled

=============================================================================
