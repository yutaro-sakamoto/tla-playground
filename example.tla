----------------- MODULE example ----------------
EXTENDS Integers, TLC, Sequences

STATE_OPEN == "open"
STATE_CLOSE == "close"
OPEN_MODE_INPUT == "input"
OPEN_MODE_OUTPUT == "output"
OPEN_MODE_I_O == "I/O"

OPEN_MODE_EXTEND == "extend"
OPERATION_WRITE == "write"
OPERATION_READ_WITH_LOCK == "read_lock"
OPERATION_READ_WITH_NO_LOCK == "read_no_lock"
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
    OPEN_MODE_INPUT |-> {OPERATION_READ_WITH_LOCK, OPERATION_READ_WITH_NO_LOCK},
    OPEN_MODE_OUTPUT |-> {OPERATION_WRITE},
    OPEN_MODE_I_O |-> {OPERATION_READ_WITH_LOCK, OPERATION_READ_WITH_NO_LOCK, OPERATION_REWRITE, OPERATION_DELETE},
    OPEN_MODE_EXTEND |-> {OPERATION_WRITE}
]

None == 0

RECORD_NOT_EXISTS == -1
RECORD_NOT_LOCKED == -2

maxPrograms == 4
programs == 1..maxPrograms

maxKeys == 3
keys == 1..maxKeys

(*--algorithm example

variables
    fileLockTable = <<>>,
    recordLock = [ key \in keys |-> RECORD_NOT_EXISTS ];

define
    atMostOneProgramOpensOutput ==
        Len(SelectSeq(fileLockTable, LAMBDA entry: entry[2] = OPEN_MODE_OUTPUT)) <= 1
end define;

process program \in programs
variables state = STATE_CLOSE, prevLockRecord
begin
    OPERATE:
        (* open a file*)
        if state = STATE_CLOSE then
            if ~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT then 
                with open_mode \in OPEN_MODE do
                    fileLockTable := SortSeq(Append(fileLockTable, <<self, open_mode>>), LAMBDA x, y: x[1] < y[1]);
                    state := STATE_OPEN;
                    prevLockRecord := None;
                end with;
            end if;
        (* close a file*)
        else
            with operation \in {OPERATION_WRITE, OPERATION_READ_WITH_NO_LOCK, OPERATION_READ_WITH_LOCK, OPERATION_REWRITE, OPERATION_DELETE, OPERATION_CLOSE} do
                assert state = STATE_OPEN;
                if operation = OPERATION_CLOSE then
                    fileLockTable := SortSeq(SelectSeq(fileLockTable, LAMBDA entry: entry[1] /= self), LAMBDA x, y: x[1] < y[1]);
                    recordLock := [key \in keys |-> 
                        IF recordLock[key] = self 
                        THEN None 
                        ELSE recordLock[key]
                    ];
                    state := STATE_CLOSE;
                elsif operation = OPERATION_WRITE then
                    if {key \in keys: recordLock[key] = RECORD_NOT_EXISTS} /= {} then
                        with key \in {key \in keys: recordLock[key] = RECORD_NOT_EXISTS} do
                            if prevLockRecord = None then
                                recordLock[key] := RECORD_NOT_LOCKED;
                            else
                                recordLock := [recordLock
                                    EXCEPT ![key] = RECORD_NOT_LOCKED,
                                           ![prevLockRecord] = RECORD_NOT_LOCKED];
                            end if;
                        end with;
                    end if;
                elsif operation = OPERATION_DELETE then
                    if {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {} then
                        with key \in {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} do
                            if recordLock[key] = RECORD_NOT_LOCKED \/ recordLock[key] = self then
                                if prevLockRecord = None then
                                    recordLock[key] := RECORD_NOT_EXISTS;
                                else
                                    recordLock := [recordLock
                                        EXCEPT ![key] = RECORD_NOT_EXISTS,
                                               ![prevLockRecord] = RECORD_NOT_LOCKED];
                                end if;
                                prevLockRecord := None;
                            else
                                skip;
                            end if;
                        end with;
                    end if;
                elsif operation = OPERATION_READ_WITH_NO_LOCK then
                    if {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {} then
                        recordLock[prevLockRecord] := RECORD_NOT_LOCKED;
                        prevLockRecord := None;
                    end if;
                end if;
            end with;
        end if;
        goto OPERATE;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES pc, fileLockTable, recordLock

(* define statement *)
atMostOneProgramOpensOutput ==
    Len(SelectSeq(fileLockTable, LAMBDA entry: entry[2] = OPEN_MODE_OUTPUT)) <= 1

VARIABLES state, prevLockRecord

vars == << pc, fileLockTable, recordLock, state, prevLockRecord >>

ProcSet == (programs)

Init == (* Global variables *)
        /\ fileLockTable = <<>>
        /\ recordLock = [ key \in keys |-> RECORD_NOT_EXISTS ]
        (* Process program *)
        /\ state = [self \in programs |-> STATE_CLOSE]
        /\ prevLockRecord = [self \in programs |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "OPERATE"]

OPERATE(self) == /\ pc[self] = "OPERATE"
                 /\ IF state[self] = STATE_CLOSE
                       THEN /\ IF ~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT
                                  THEN /\ \E open_mode \in OPEN_MODE:
                                            /\ fileLockTable' = SortSeq(Append(fileLockTable, <<self, open_mode>>), LAMBDA x, y: x[1] < y[1])
                                            /\ state' = [state EXCEPT ![self] = STATE_OPEN]
                                            /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = None]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << fileLockTable, state, 
                                                       prevLockRecord >>
                            /\ UNCHANGED recordLock
                       ELSE /\ \E operation \in {OPERATION_WRITE, OPERATION_READ_WITH_NO_LOCK, OPERATION_READ_WITH_LOCK, OPERATION_REWRITE, OPERATION_DELETE, OPERATION_CLOSE}:
                                 /\ Assert(state[self] = STATE_OPEN, 
                                           "Failure of assertion at line 70, column 17.")
                                 /\ IF operation = OPERATION_CLOSE
                                       THEN /\ fileLockTable' = SortSeq(SelectSeq(fileLockTable, LAMBDA entry: entry[1] /= self), LAMBDA x, y: x[1] < y[1])
                                            /\ recordLock' =               [key \in keys |->
                                                                 IF recordLock[key] = self
                                                                 THEN None
                                                                 ELSE recordLock[key]
                                                             ]
                                            /\ state' = [state EXCEPT ![self] = STATE_CLOSE]
                                            /\ UNCHANGED prevLockRecord
                                       ELSE /\ IF operation = OPERATION_WRITE
                                                  THEN /\ IF {key \in keys: recordLock[key] = RECORD_NOT_EXISTS} /= {}
                                                             THEN /\ \E key \in {key \in keys: recordLock[key] = RECORD_NOT_EXISTS}:
                                                                       IF prevLockRecord[self] = None
                                                                          THEN /\ recordLock' = [recordLock EXCEPT ![key] = RECORD_NOT_LOCKED]
                                                                          ELSE /\ recordLock' =           [recordLock
                                                                                                EXCEPT ![key] = RECORD_NOT_LOCKED,
                                                                                                       ![prevLockRecord[self]] = RECORD_NOT_LOCKED]
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED recordLock
                                                       /\ UNCHANGED prevLockRecord
                                                  ELSE /\ IF operation = OPERATION_DELETE
                                                             THEN /\ IF {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {}
                                                                        THEN /\ \E key \in {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS}:
                                                                                  IF recordLock[key] = RECORD_NOT_LOCKED \/ recordLock[key] = self
                                                                                     THEN /\ IF prevLockRecord[self] = None
                                                                                                THEN /\ recordLock' = [recordLock EXCEPT ![key] = RECORD_NOT_EXISTS]
                                                                                                ELSE /\ recordLock' =           [recordLock
                                                                                                                      EXCEPT ![key] = RECORD_NOT_EXISTS,
                                                                                                                             ![prevLockRecord[self]] = RECORD_NOT_LOCKED]
                                                                                          /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = None]
                                                                                     ELSE /\ TRUE
                                                                                          /\ UNCHANGED << recordLock, 
                                                                                                          prevLockRecord >>
                                                                        ELSE /\ TRUE
                                                                             /\ UNCHANGED << recordLock, 
                                                                                             prevLockRecord >>
                                                             ELSE /\ IF operation = OPERATION_READ_WITH_NO_LOCK
                                                                        THEN /\ IF {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {}
                                                                                   THEN /\ recordLock' = [recordLock EXCEPT ![prevLockRecord[self]] = RECORD_NOT_LOCKED]
                                                                                        /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = None]
                                                                                   ELSE /\ TRUE
                                                                                        /\ UNCHANGED << recordLock, 
                                                                                                        prevLockRecord >>
                                                                        ELSE /\ TRUE
                                                                             /\ UNCHANGED << recordLock, 
                                                                                             prevLockRecord >>
                                            /\ UNCHANGED << fileLockTable, 
                                                            state >>
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
