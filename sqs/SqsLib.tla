------------------------------ MODULE SqsLib ------------------------------
(***************************************************************************)
(* SQS のセマンティクスを「純粋な演算子」として提供するライブラリ。         *)
(*                                                                         *)
(* PlusCal 側は状態変数 sqs を 1 つ持ち、ここの演算子で更新するだけ。       *)
(*   - 可視性タイムアウト : 実時間ではなく「いつでも起こりうる」遷移で表す   *)
(*   - 受信ハンドル       : 受信ごとに新しい rh。古い rh での削除は no-op    *)
(*   - DLQ                : 受信回数が MaxReceive に達した可視メッセージを   *)
(*                          Redrive[q] で指定した DLQ に移す                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Redrive,     \* [ソースキュー -> DLQ 名]。DOMAIN に無いキューは DLQ なし
    MaxReceive   \* リドライブポリシーの maxReceiveCount

----------------------------------------------------------------------------
(* 状態: msgs は ID -> メッセージ の関数、next は次に払い出す ID          *)
(* メッセージ: [q, body, rc(受信回数), visible, rh(現在の受信ハンドル)]    *)

Empty == [msgs |-> [i \in {} |-> 0], next |-> 1]

\* Lambda が持つ「受信したメッセージ」の控え
NoHandle == [id |-> 0, rh |-> 0, body |-> "none"]

HasDLQ(q) == q \in DOMAIN Redrive

----------------------------------------------------------------------------
(* 送信                                                                    *)

Send(s, q, body) ==
    [msgs |-> s.msgs @@ (s.next :> [q |-> q, body |-> body, rc |-> 0,
                                   visible |-> TRUE, rh |-> 0]),
     next |-> s.next + 1]

\* out は << [q |-> キュー名, body |-> 本文], ... >> の列
RECURSIVE SendAll(_, _)
SendAll(s, out) ==
    IF out = << >> THEN s
    ELSE SendAll(Send(s, Head(out).q, Head(out).body), Tail(out))

\* 初期投入用: 集合 bodies をすべて q に送る
RECURSIVE SendSet(_, _, _)
SendSet(s, q, bodies) ==
    IF bodies = {} THEN s
    ELSE LET b == CHOOSE x \in bodies : TRUE
         IN  SendSet(Send(s, q, b), q, bodies \ {b})

----------------------------------------------------------------------------
(* 受信・削除                                                              *)

\* 今 q から受信できるメッセージ ID の集合
\* (受信上限に達したものは、DLQ があれば次の受信時に DLQ 行きなので除外)
Receivable(s, q) ==
    { id \in DOMAIN s.msgs :
        LET m == s.msgs[id]
        IN  m.q = q /\ m.visible /\ (m.rc < MaxReceive \/ ~HasDLQ(q)) }

\* 受信: 受信回数を増やし、不可視にし、新しい受信ハンドルを発行
Receive(s, id) ==
    LET m == s.msgs[id]
    IN  [s EXCEPT !.msgs[id] = [m EXCEPT !.rc = m.rc + 1,
                                         !.visible = FALSE,
                                         !.rh = m.rc + 1]]

\* 受信直後の状態 s から、Lambda が保持する控えを作る
HandleOf(s, id) == [id |-> id, rh |-> s.msgs[id].rh, body |-> s.msgs[id].body]

\* 削除: 最新の受信ハンドルでなければ何も起きない(古いハンドルは無効)
Delete(s, h) ==
    IF h.id \in DOMAIN s.msgs /\ s.msgs[h.id].rh = h.rh
    THEN [s EXCEPT !.msgs = [i \in DOMAIN s.msgs \ {h.id} |-> s.msgs[i]]]
    ELSE s

----------------------------------------------------------------------------
(* インフラ側で自発的に起こる遷移(Infra プロセスが 1 つずつ選んで実行)      *)

\* 可視性タイムアウト: 処理中かどうかに関係なく、いつでも切れうる
Timeouts(s) ==
    { [s EXCEPT !.msgs[id].visible = TRUE] :
        id \in { i \in DOMAIN s.msgs : ~s.msgs[i].visible } }

\* DLQ への移動(本物の SQS では受信試行時に起きるが、抽象化して自発遷移に)
DLQMoves(s) ==
    { [s EXCEPT !.msgs[id] = [s.msgs[id] EXCEPT !.q = Redrive[s.msgs[id].q],
                                                !.rc = 0, !.rh = 0]] :
        id \in { i \in DOMAIN s.msgs :
                   LET m == s.msgs[i]
                   IN  m.visible /\ HasDLQ(m.q) /\ m.rc >= MaxReceive } }

InfraNext(s) == Timeouts(s) \cup DLQMoves(s)

----------------------------------------------------------------------------
(* 性質を書くための補助                                                    *)

BodiesIn(s, q) == { s.msgs[id].body : id \in { i \in DOMAIN s.msgs : s.msgs[i].q = q } }

Drained(s, qs) == \A id \in DOMAIN s.msgs : s.msgs[id].q \notin qs

=============================================================================
