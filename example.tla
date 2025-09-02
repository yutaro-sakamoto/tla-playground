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
    mode \in {OPEN_MODE_INPUT, OPEN_MODE_OUTPUT, OPEN_MODE_I_O, OPEN_MODE_EXTEND} |->
    IF mode = OPEN_MODE_INPUT THEN
        {OPERATION_READ_WITH_LOCK, OPERATION_READ_WITH_NO_LOCK}
    ELSE IF mode = OPEN_MODE_OUTPUT THEN
        {OPERATION_WRITE}
    ELSE IF mode = OPEN_MODE_I_O THEN
        {OPERATION_READ_WITH_LOCK, OPERATION_READ_WITH_NO_LOCK, OPERATION_REWRITE, OPERATION_DELETE}
    ELSE
        {OPERATION_WRITE}
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
variables state = STATE_CLOSE, open_mode = OPEN_MODE_INPUT, prevLockRecord = None
begin
    OPERATE:
        (* open a file*)
        if state = STATE_CLOSE then
            if ~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT then 
                with mode \in OPEN_MODE do
                    fileLockTable := SortSeq(Append(fileLockTable, <<self, open_mode>>), LAMBDA x, y: x[1] < y[1]);
                    state := STATE_OPEN;
                    prevLockRecord := None;
                    open_mode := mode;
                end with;
            end if;
        (* close a file*)
        else
            with operation \in ALLOWED_OPERATIONS[open_mode] do
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
VARIABLES pc, fileLockTable, recordLock

(* define statement *)
atMostOneProgramOpensOutput ==
    Len(SelectSeq(fileLockTable, LAMBDA entry: entry[2] = OPEN_MODE_OUTPUT)) <= 1

VARIABLES state, open_mode, prevLockRecord

vars == << pc, fileLockTable, recordLock, state, open_mode, prevLockRecord >>

ProcSet == (programs)

Init == (* Global variables *)
        /\ fileLockTable = <<>>
        /\ recordLock = [ key \in keys |-> RECORD_NOT_EXISTS ]
        (* Process program *)
        /\ state = [self \in programs |-> STATE_CLOSE]
        /\ open_mode = [self \in programs |-> OPEN_MODE_INPUT]
        /\ prevLockRecord = [self \in programs |-> None]
        /\ pc = [self \in ProcSet |-> "OPERATE"]

OPERATE(self) == /\ pc[self] = "OPERATE"
                 /\ IF state[self] = STATE_CLOSE
                       THEN /\ IF ~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT
                                  THEN /\ \E mode \in OPEN_MODE:
                                            /\ fileLockTable' = SortSeq(Append(fileLockTable, <<self, open_mode[self]>>), LAMBDA x, y: x[1] < y[1])
                                            /\ state' = [state EXCEPT ![self] = STATE_OPEN]
                                            /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = None]
                                            /\ open_mode' = [open_mode EXCEPT ![self] = mode]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << fileLockTable, state, 
                                                       open_mode, 
                                                       prevLockRecord >>
                            /\ UNCHANGED recordLock
                       ELSE /\ \E operation \in ALLOWED_OPERATIONS[open_mode[self]]:
                                 /\ Assert(state[self] = STATE_OPEN, 
                                           "Failure of assertion at line 76, column 17.")
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
                            /\ UNCHANGED open_mode
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
