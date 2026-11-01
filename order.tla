----------------- MODULE order ----------------
EXTENDS Integers, TLC, Sequences, FiniteSets

MAX_REQUEST_COUNT == 5
STOCK_INITIAL == 3

LAMBDA_A_MAX_COUNTS == 2
LAMBDA_B_MAX_COUNTS == 3

ORDER_TYPES == { "A", "B", "C" }

(*--algorithm example

variables
    sqs1 = <<>>,
    dlq1 = <<>>,
    sqs2 = <<>>,
    stock = STOCK_INITIAL,
    reserved = [i \in ORDER_TYPES |-> 0],
    requestCounts = 0;

define
    stockIsNotNegative == stock >= 0
LAMBDA_A_PROCS ==
  { "Lambda_A_" \o ToString(i) : i \in 1 .. LAMBDA_A_MAX_COUNTS }
LAMBDA_B_PROCS ==
  { "Lambda_B_" \o ToString(i) : i \in 1 .. LAMBDA_B_MAX_COUNTS }
end define;

process LambdaA \in LAMBDA_A_PROCS
begin
WHILE_LABEL:
    while requestCounts < MAX_REQUEST_COUNT do 
        either
            sqs1 := Append(sqs1, requestCounts);
            with order_type \in ORDER_TYPES do
                reserved[order_type] := reserved[order_type] + 1;
            end with;
        or
            sqs1 := sqs1 \o <<requestCounts, requestCounts>>;
            with order_type \in ORDER_TYPES do
                reserved[order_type] := reserved[order_type] + 1;
            end with;
        or
            skip;
        end either;
        requestCounts := requestCounts + 1;
    end while;
end process;

process LambdaB \in LAMBDA_B_PROCS
begin
WHILE_LABEL:
    while requestCounts < MAX_REQUEST_COUNT do
        await sqs1 # <<>>;
        either
            if stock > 0 then 
                stock := stock - 1;
            end if;
        or
            \* dlq
            dlq1 := Append(dlq1, sqs1[1]);
        end either;
        sqs1 := Tail(sqs1)
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
\* Label WHILE_LABEL of process LambdaA at line 33 col 5 changed to WHILE_LABEL_
VARIABLES pc, sqs1, dlq1, sqs2, stock, reserved, requestCounts

(* define statement *)
    stockIsNotNegative == stock >= 0
LAMBDA_A_PROCS ==
  { "Lambda_A_" \o ToString(i) : i \in 1 .. LAMBDA_A_MAX_COUNTS }
LAMBDA_B_PROCS ==
  { "Lambda_B_" \o ToString(i) : i \in 1 .. LAMBDA_B_MAX_COUNTS }


vars == << pc, sqs1, dlq1, sqs2, stock, reserved, requestCounts >>

ProcSet == (LAMBDA_A_PROCS) \cup (LAMBDA_B_PROCS)

Init == (* Global variables *)
        /\ sqs1 = <<>>
        /\ dlq1 = <<>>
        /\ sqs2 = <<>>
        /\ stock = STOCK_INITIAL
        /\ reserved = [i \in ORDER_TYPES |-> 0]
        /\ requestCounts = 0
        /\ pc = [self \in ProcSet |-> CASE self \in LAMBDA_A_PROCS -> "WHILE_LABEL_"
                                        [] self \in LAMBDA_B_PROCS -> "WHILE_LABEL"]

WHILE_LABEL_(self) == /\ pc[self] = "WHILE_LABEL_"
                      /\ IF requestCounts < MAX_REQUEST_COUNT
                            THEN /\ \/ /\ sqs1' = Append(sqs1, requestCounts)
                                       /\ \E order_type \in ORDER_TYPES:
                                            reserved' = [reserved EXCEPT ![order_type] = reserved[order_type] + 1]
                                    \/ /\ sqs1' = sqs1 \o <<requestCounts, requestCounts>>
                                       /\ \E order_type \in ORDER_TYPES:
                                            reserved' = [reserved EXCEPT ![order_type] = reserved[order_type] + 1]
                                    \/ /\ TRUE
                                       /\ UNCHANGED <<sqs1, reserved>>
                                 /\ requestCounts' = requestCounts + 1
                                 /\ pc' = [pc EXCEPT ![self] = "WHILE_LABEL_"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED << sqs1, reserved, requestCounts >>
                      /\ UNCHANGED << dlq1, sqs2, stock >>

LambdaA(self) == WHILE_LABEL_(self)

WHILE_LABEL(self) == /\ pc[self] = "WHILE_LABEL"
                     /\ IF requestCounts < MAX_REQUEST_COUNT
                           THEN /\ sqs1 # <<>>
                                /\ \/ /\ IF stock > 0
                                            THEN /\ stock' = stock - 1
                                            ELSE /\ TRUE
                                                 /\ stock' = stock
                                      /\ dlq1' = dlq1
                                   \/ /\ dlq1' = Append(dlq1, sqs1[1])
                                      /\ stock' = stock
                                /\ sqs1' = Tail(sqs1)
                                /\ pc' = [pc EXCEPT ![self] = "WHILE_LABEL"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << sqs1, dlq1, stock >>
                     /\ UNCHANGED << sqs2, reserved, requestCounts >>

LambdaB(self) == WHILE_LABEL(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in LAMBDA_A_PROCS: LambdaA(self))
           \/ (\E self \in LAMBDA_B_PROCS: LambdaB(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=======================
