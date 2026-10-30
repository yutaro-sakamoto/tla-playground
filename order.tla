----------------- MODULE order ----------------
EXTENDS Integers, TLC, Sequences, FiniteSets

MAX_REQUEST_COUNT == 10


(*--algorithm example

variables
    sqs1 = <<>>,
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

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES pc, sqs1, sqs2, requestCounts

vars == << pc, sqs1, sqs2, requestCounts >>

ProcSet == {"LambdaA"}

Init == (* Global variables *)
        /\ sqs1 = <<>>
        /\ sqs2 = <<>>
        /\ requestCounts = 0
        /\ pc = [self \in ProcSet |-> "WHILE_LABEL"]

WHILE_LABEL == /\ pc["LambdaA"] = "WHILE_LABEL"
               /\ IF requestCounts < MAX_REQUEST_COUNT
                     THEN /\ \/ /\ sqs1' = Append(sqs1, requestCounts)
                             \/ /\ TRUE
                                /\ sqs1' = sqs1
                          /\ requestCounts' = requestCounts + 1
                          /\ pc' = [pc EXCEPT !["LambdaA"] = "WHILE_LABEL"]
                     ELSE /\ pc' = [pc EXCEPT !["LambdaA"] = "Done"]
                          /\ UNCHANGED << sqs1, requestCounts >>
               /\ sqs2' = sqs2

LambdaA == WHILE_LABEL

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == LambdaA
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=======================
