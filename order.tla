----------------- MODULE order ----------------
EXTENDS Integers, TLC, Sequences, FiniteSets

MAX_REQUEST_COUNT == 10


(*--algorithm example

variables
    sqs1 = <<>>,
    dlq1 = <<>>,
    sqs2 = <<>>,
    requestCounts = 0;

process LambdaA = "LambdaA"
begin
WHILE_LABEL:
    while requestCounts < MAX_REQUEST_COUNT do 
        either
            sqs1 := Append(sqs1, requestCounts);
        or
            skip;
        end either;
        requestCounts := requestCounts + 1;
    end while;
end process;

process LambdaB = "LambdaB"
begin
WHILE_LABEL:
    while requestCounts < MAX_REQUEST_COUNT do
        await sqs1 # <<>>;
        either
            \* consume
            skip;
        or
            \* dlq
            dlq1 := Append(dlq1, sqs1[1]);
        end either;
        sqs1 := Tail(sqs1)
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
\* Label WHILE_LABEL of process LambdaA at line 18 col 5 changed to WHILE_LABEL_
VARIABLES pc, sqs1, dlq1, sqs2, requestCounts

vars == << pc, sqs1, dlq1, sqs2, requestCounts >>

ProcSet == {"LambdaA"} \cup {"LambdaB"}

Init == (* Global variables *)
        /\ sqs1 = <<>>
        /\ dlq1 = <<>>
        /\ sqs2 = <<>>
        /\ requestCounts = 0
        /\ pc = [self \in ProcSet |-> CASE self = "LambdaA" -> "WHILE_LABEL_"
                                        [] self = "LambdaB" -> "WHILE_LABEL"]

WHILE_LABEL_ == /\ pc["LambdaA"] = "WHILE_LABEL_"
                /\ IF requestCounts < MAX_REQUEST_COUNT
                      THEN /\ \/ /\ sqs1' = Append(sqs1, requestCounts)
                              \/ /\ TRUE
                                 /\ sqs1' = sqs1
                           /\ requestCounts' = requestCounts + 1
                           /\ pc' = [pc EXCEPT !["LambdaA"] = "WHILE_LABEL_"]
                      ELSE /\ pc' = [pc EXCEPT !["LambdaA"] = "Done"]
                           /\ UNCHANGED << sqs1, requestCounts >>
                /\ UNCHANGED << dlq1, sqs2 >>

LambdaA == WHILE_LABEL_

WHILE_LABEL == /\ pc["LambdaB"] = "WHILE_LABEL"
               /\ IF requestCounts < MAX_REQUEST_COUNT
                     THEN /\ sqs1 # <<>>
                          /\ \/ /\ TRUE
                                /\ dlq1' = dlq1
                             \/ /\ dlq1' = Append(dlq1, sqs1[1])
                          /\ sqs1' = Tail(sqs1)
                          /\ pc' = [pc EXCEPT !["LambdaB"] = "WHILE_LABEL"]
                     ELSE /\ pc' = [pc EXCEPT !["LambdaB"] = "Done"]
                          /\ UNCHANGED << sqs1, dlq1 >>
               /\ UNCHANGED << sqs2, requestCounts >>

LambdaB == WHILE_LABEL

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == LambdaA \/ LambdaB
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=======================
