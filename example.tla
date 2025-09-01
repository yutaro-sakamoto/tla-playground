----------------- MODULE example ----------------
EXTENDS Integers, TLC, Sequences

STATE_OPEN == "open"
STATE_CLOSE == "close"
OPEN_MODE_INPUT == "input"
OPEN_MODE_OUTPUT == "output"
OPEN_MODE_I_O == "I/O"

OPEN_MODE_EXTEND == "extend"
OPERATION_WRITE == "write"
OPERATION_READ == "read"
OPERATION_REWRITE == "rewrite"
OPERATION_DELETE == "delete"
OPERATION_CLOSE == "close"

OPEN_MODE == {
    OPEN_MODE_INPUT,
    OPEN_MODE_OUTPUT, 
    OPEN_MODE_I_O,
    OPEN_MODE_EXTEND
}

ALLOWED_OPERATIONS == [
    OPEN_MODE_INPUT |-> {OPERATION_READ},
    OPEN_MODE_OUTPUT |-> {OPERATION_WRITE},
    OPEN_MODE_I_O |-> {OPERATION_READ, OPERATION_REWRITE, OPERATION_DELETE},
    OPEN_MODE_EXTEND |-> {OPERATION_WRITE}
]

None == 0

maxPrograms == 4
programs == 1..maxPrograms

maxKeys == 3
keys == 1..maxKeys

(*--algorithm example

variables
    fileLockTable = <<>>,
    recordLock = <<>>;

define
    atMostOneProgramOpensOutput ==
        Len(SelectSeq(fileLockTable, LAMBDA entry: entry[2] = OPEN_MODE_OUTPUT)) <= 1
end define;

process program \in programs
variables state = STATE_CLOSE
begin
    OPERATE:
        (* open a file*)
        if state = STATE_CLOSE then
            if ~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT then 
                with open_mode \in OPEN_MODE do
                    fileLockTable := SortSeq(Append(fileLockTable, <<self, open_mode>>), LAMBDA x, y: x[1] < y[1]);
                    state := STATE_OPEN;
                end with;
            end if;
        (* close a file*)
        else
            with operation \in {OPERATION_WRITE, OPERATION_READ, OPERATION_REWRITE, OPERATION_DELETE, OPERATION_CLOSE} do
                assert state = STATE_OPEN;
                if operation = OPERATION_CLOSE then
                    fileLockTable := SortSeq(SelectSeq(fileLockTable, LAMBDA entry: entry[1] /= self), LAMBDA x, y: x[1] < y[1]);
                    recordLock := [i \in 1..Len(recordLock) |-> 
                        IF recordLock[i][2] = self 
                        THEN <<recordLock[i][1], None>> 
                        ELSE recordLock[i]];
                    state := STATE_CLOSE;
                elsif operation = OPERATION_WRITE then
                    skip;
                end if
            end with;
        end if;
        goto OPERATE;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES pc, fileLockTable, recordLock

(* define statement *)
atMostOneProgramOpensOutput ==
    Len(SelectSeq(fileLockTable, LAMBDA entry: entry[2] = OPEN_MODE_OUTPUT)) <= 1

VARIABLE state

vars == << pc, fileLockTable, recordLock, state >>

ProcSet == (programs)

Init == (* Global variables *)
        /\ fileLockTable = <<>>
        /\ recordLock = <<>>
        (* Process program *)
        /\ state = [self \in programs |-> STATE_CLOSE]
        /\ pc = [self \in ProcSet |-> "OPERATE"]

OPERATE(self) == /\ pc[self] = "OPERATE"
                 /\ IF state[self] = STATE_CLOSE
                       THEN /\ IF ~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT
                                  THEN /\ \E open_mode \in OPEN_MODE:
                                            /\ fileLockTable' = SortSeq(Append(fileLockTable, <<self, open_mode>>), LAMBDA x, y: x[1] < y[1])
                                            /\ state' = [state EXCEPT ![self] = STATE_OPEN]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << fileLockTable, state >>
                            /\ UNCHANGED recordLock
                       ELSE /\ \E operation \in {OPERATION_WRITE, OPERATION_READ, OPERATION_REWRITE, OPERATION_DELETE, OPERATION_CLOSE}:
                                 /\ Assert(state[self] = STATE_OPEN, 
                                           "Failure of assertion at line 65, column 17.")
                                 /\ IF operation = OPERATION_CLOSE
                                       THEN /\ fileLockTable' = SortSeq(SelectSeq(fileLockTable, LAMBDA entry: entry[1] /= self), LAMBDA x, y: x[1] < y[1])
                                            /\ recordLock' =           [i \in 1..Len(recordLock) |->
                                                             IF recordLock[i][2] = self
                                                             THEN <<recordLock[i][1], None>>
                                                             ELSE recordLock[i]]
                                            /\ state' = [state EXCEPT ![self] = STATE_CLOSE]
                                       ELSE /\ IF operation = OPERATION_WRITE
                                                  THEN /\ TRUE
                                                  ELSE /\ TRUE
                                            /\ UNCHANGED << fileLockTable, 
                                                            recordLock, state >>
                 /\ pc' = [pc EXCEPT ![self] = "OPERATE"]

program(self) == OPERATE(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in programs: program(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=======================
