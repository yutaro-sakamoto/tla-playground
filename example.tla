----------------- MODULE example ----------------
EXTENDS Integers, TLC, Sequences, FiniteSets

STATE_OPEN == "open"
STATE_CLOSE == "close"
OPEN_MODE_INPUT == "input"
OPEN_MODE_OUTPUT == "output"
OPEN_MODE_I_O == "I/O"
OPEN_MODE_EXTEND == "extend"

OPERATION_OPEN == "open"
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
        {OPERATION_READ_WITH_NO_LOCK}
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
    (* OPEN OUTPUTで開いているプログラムがあるなら、ファイルを開いているプログラムはただ1つ *)
    ifOneProgramOpenOutputNoOtherOpen ==
        (\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT) =>
            Len(fileLockTable) = 1
    (* OPEN OUTPUTで開いているプログラムがあるなら、ロックされているレコードはない *)
    ifOneProgramOpenOutputNoRecordIsLocked ==
        (\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT) =>
            \A key \in keys: ~(recordLock[key] \in programs)
    (* レコードをロックしているプログラムは、FileLockTableにI-Oモードで開いていると記録されている *)
    allLockedRecordLockedByProgramWithOpenIO ==
        \A key \in keys:
            (recordLock[key] \in programs) =>
                LET lst == SelectSeq(fileLockTable, LAMBDA entry: entry[1] = recordLock[key])
                 IN \A i \in 1..Len(lst):
                    lst[i][2] = OPEN_MODE_I_O
    (* それぞれのプログラムは、高々1つのレコードだけをロックする *)
    eachProgramLocksAtMostOneRecord ==
        \A p \in programs:
            LET lst == { key \in keys: recordLock[key] = p }
             IN Cardinality(lst) <= 1
    (* 各プログラムに対応するfileLockTable中のエントリーは高々1つ *)
    eachProgramHasAtMostOneFileLockTableEntry ==
        \A p \in programs:
            Cardinality({ i \in 1..Len(fileLockTable): fileLockTable[i][1] = p }) <= 1
    (* OPEN I-Oで開いているプログラムがないなら、ロックされたレコードは存在しない *)
    ifNoProgramOpensIONoRecordIsLocked ==
        (~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_I_O) =>
            \A key \in keys: ~(recordLock[key] \in programs)
end define;

process program \in programs
variables state = STATE_CLOSE, open_mode = OPEN_MODE_INPUT, prevLockRecord = None, lastOperation
begin
    OPERATE:
        (* open a file*)
        if state = STATE_CLOSE then
            lastOperation := OPERATION_OPEN;

            (* Just before a program opens a file, the file must not be opened by the program *)
            assert ~\E i \in 1..Len(fileLockTable): fileLockTable[i][1] = self;

            (* Just before a program opens a file, no record must be locked by the program *)
            assert ~\E key \in keys: recordLock[key] = self;

            with mode \in OPEN_MODE do
                if mode = OPEN_MODE_OUTPUT then
                    if fileLockTable = <<>> then
                        state := STATE_OPEN;
                        prevLockRecord := None;
                        open_mode := mode;
                    end if;
                elsif ~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT then 
                        fileLockTable := SortSeq(Append(fileLockTable, <<self, mode>>), LAMBDA x, y: x[1] < y[1]);
                        state := STATE_OPEN;
                        prevLockRecord := None;
                        open_mode := mode;
                end if;
            end with;
        else
            with operation \in ALLOWED_OPERATIONS[open_mode] do
                assert state = STATE_OPEN;
                (* close a file*)
                if operation = OPERATION_CLOSE then
                    lastOperation := OPERATION_CLOSE;
                    fileLockTable := SortSeq(SelectSeq(fileLockTable, LAMBDA entry: entry[1] /= self), LAMBDA x, y: x[1] < y[1]);
                    recordLock := [key \in keys |-> 
                        IF recordLock[key] = self 
                        THEN None 
                        ELSE recordLock[key]
                    ];
                    state := STATE_CLOSE;
                (* write a record *)
                elsif operation = OPERATION_WRITE then
                    lastOperation := OPERATION_WRITE;
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
                (* delete a record *)
                elsif operation = OPERATION_DELETE then
                    lastOperation := OPERATION_DELETE;
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
                (* read a record without locking it *)
                elsif operation = OPERATION_READ_WITH_NO_LOCK then
                    lastOperation := OPERATION_READ_WITH_NO_LOCK;
                    if {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {} then
                        if prevLockRecord /= None then
                            recordLock[prevLockRecord] := RECORD_NOT_LOCKED;
                        end if;
                        prevLockRecord := None;
                    end if;
                (* read a record and lock it *)
                elsif operation = OPERATION_READ_WITH_LOCK then
                    lastOperation := OPERATION_READ_WITH_LOCK;
                    if {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {} then
                        with key \in {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} do
                            (* success to lock record lock *)
                            if recordLock[key] = RECORD_NOT_LOCKED \/ recordLock[key] = self then
                                if prevLockRecord = None then
                                    recordLock[key] := self;
                                    prevLockRecord := key;
                                elsif prevLockRecord = key then
                                    prevLockRecord := key;
                                else
                                    recordLock := [recordLock
                                        EXCEPT ![key] = self,
                                               ![prevLockRecord] = RECORD_NOT_LOCKED];
                                    prevLockRecord := key;
                                end if;
                            (* failed to lock record locked *)
                            else
                                if prevLockRecord /= None then
                                    recordLock[prevLockRecord] := RECORD_NOT_LOCKED;
                                    prevLockRecord := None;
                                end if;
                            end if;
                        end with;
                    end if;
                (* rewrite a record *)
                elsif operation = OPERATION_REWRITE then
                    lastOperation := OPERATION_REWRITE;
                    if {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {} then
                        with key \in {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} do
                            if recordLock[key] = self \/ recordLock[key] = RECORD_NOT_LOCKED then
                                (* rewrite the record *)
                                skip;
                                (* unlock previously locked record *)
                                if prevLockRecord /= None then
                                    recordLock[prevLockRecord] := RECORD_NOT_LOCKED;
                                end if;
                            else
                                (* cannot rewrite a record locked by another process *)
                                if prevLockRecord /= None then
                                    recordLock[prevLockRecord] := RECORD_NOT_LOCKED;
                                end if;
                            end if;
                        end with;
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
ifOneProgramOpenOutputNoOtherOpen ==
    (\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT) =>
        Len(fileLockTable) = 1

ifOneProgramOpenOutputNoRecordIsLocked ==
    (\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT) =>
        \A key \in keys: ~(recordLock[key] \in programs)

allLockedRecordLockedByProgramWithOpenIO ==
    \A key \in keys:
        (recordLock[key] \in programs) =>
            LET lst == SelectSeq(fileLockTable, LAMBDA entry: entry[1] = recordLock[key])
             IN \A i \in 1..Len(lst):
                lst[i][2] = OPEN_MODE_I_O

eachProgramLocksAtMostOneRecord ==
    \A p \in programs:
        LET lst == { key \in keys: recordLock[key] = p }
         IN Cardinality(lst) <= 1

eachProgramHasAtMostOneFileLockTableEntry ==
    \A p \in programs:
        Cardinality({ i \in 1..Len(fileLockTable): fileLockTable[i][1] = p }) <= 1

ifNoProgramOpensIONoRecordIsLocked ==
    (~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_I_O) =>
        \A key \in keys: ~(recordLock[key] \in programs)

VARIABLES state, open_mode, prevLockRecord, lastOperation

vars == << pc, fileLockTable, recordLock, state, open_mode, prevLockRecord, 
           lastOperation >>

ProcSet == (programs)

Init == (* Global variables *)
        /\ fileLockTable = <<>>
        /\ recordLock = [ key \in keys |-> RECORD_NOT_EXISTS ]
        (* Process program *)
        /\ state = [self \in programs |-> STATE_CLOSE]
        /\ open_mode = [self \in programs |-> OPEN_MODE_INPUT]
        /\ prevLockRecord = [self \in programs |-> None]
        /\ lastOperation = [self \in programs |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "OPERATE"]

OPERATE(self) == /\ pc[self] = "OPERATE"
                 /\ IF state[self] = STATE_CLOSE
                       THEN /\ lastOperation' = [lastOperation EXCEPT ![self] = OPERATION_OPEN]
                            /\ Assert(~\E i \in 1..Len(fileLockTable): fileLockTable[i][1] = self, 
                                      "Failure of assertion at line 95, column 13.")
                            /\ Assert(~\E key \in keys: recordLock[key] = self, 
                                      "Failure of assertion at line 98, column 13.")
                            /\ \E mode \in OPEN_MODE:
                                 IF mode = OPEN_MODE_OUTPUT
                                    THEN /\ IF fileLockTable = <<>>
                                               THEN /\ state' = [state EXCEPT ![self] = STATE_OPEN]
                                                    /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = None]
                                                    /\ open_mode' = [open_mode EXCEPT ![self] = mode]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << state, 
                                                                    open_mode, 
                                                                    prevLockRecord >>
                                         /\ UNCHANGED fileLockTable
                                    ELSE /\ IF ~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT
                                               THEN /\ fileLockTable' = SortSeq(Append(fileLockTable, <<self, mode>>), LAMBDA x, y: x[1] < y[1])
                                                    /\ state' = [state EXCEPT ![self] = STATE_OPEN]
                                                    /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = None]
                                                    /\ open_mode' = [open_mode EXCEPT ![self] = mode]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << fileLockTable, 
                                                                    state, 
                                                                    open_mode, 
                                                                    prevLockRecord >>
                            /\ UNCHANGED recordLock
                       ELSE /\ \E operation \in ALLOWED_OPERATIONS[open_mode[self]]:
                                 /\ Assert(state[self] = STATE_OPEN, 
                                           "Failure of assertion at line 116, column 17.")
                                 /\ IF operation = OPERATION_CLOSE
                                       THEN /\ lastOperation' = [lastOperation EXCEPT ![self] = OPERATION_CLOSE]
                                            /\ fileLockTable' = SortSeq(SelectSeq(fileLockTable, LAMBDA entry: entry[1] /= self), LAMBDA x, y: x[1] < y[1])
                                            /\ recordLock' =               [key \in keys |->
                                                                 IF recordLock[key] = self
                                                                 THEN None
                                                                 ELSE recordLock[key]
                                                             ]
                                            /\ state' = [state EXCEPT ![self] = STATE_CLOSE]
                                            /\ UNCHANGED prevLockRecord
                                       ELSE /\ IF operation = OPERATION_WRITE
                                                  THEN /\ lastOperation' = [lastOperation EXCEPT ![self] = OPERATION_WRITE]
                                                       /\ IF {key \in keys: recordLock[key] = RECORD_NOT_EXISTS} /= {}
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
                                                             THEN /\ lastOperation' = [lastOperation EXCEPT ![self] = OPERATION_DELETE]
                                                                  /\ IF {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {}
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
                                                                        THEN /\ lastOperation' = [lastOperation EXCEPT ![self] = OPERATION_READ_WITH_NO_LOCK]
                                                                             /\ IF {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {}
                                                                                   THEN /\ IF prevLockRecord[self] /= None
                                                                                              THEN /\ recordLock' = [recordLock EXCEPT ![prevLockRecord[self]] = RECORD_NOT_LOCKED]
                                                                                              ELSE /\ TRUE
                                                                                                   /\ UNCHANGED recordLock
                                                                                        /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = None]
                                                                                   ELSE /\ TRUE
                                                                                        /\ UNCHANGED << recordLock, 
                                                                                                        prevLockRecord >>
                                                                        ELSE /\ IF operation = OPERATION_READ_WITH_LOCK
                                                                                   THEN /\ lastOperation' = [lastOperation EXCEPT ![self] = OPERATION_READ_WITH_LOCK]
                                                                                        /\ IF {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {}
                                                                                              THEN /\ \E key \in {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS}:
                                                                                                        IF recordLock[key] = RECORD_NOT_LOCKED \/ recordLock[key] = self
                                                                                                           THEN /\ IF prevLockRecord[self] = None
                                                                                                                      THEN /\ recordLock' = [recordLock EXCEPT ![key] = self]
                                                                                                                           /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = key]
                                                                                                                      ELSE /\ IF prevLockRecord[self] = key
                                                                                                                                 THEN /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = key]
                                                                                                                                      /\ UNCHANGED recordLock
                                                                                                                                 ELSE /\ recordLock' =           [recordLock
                                                                                                                                                       EXCEPT ![key] = self,
                                                                                                                                                              ![prevLockRecord[self]] = RECORD_NOT_LOCKED]
                                                                                                                                      /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = key]
                                                                                                           ELSE /\ IF prevLockRecord[self] /= None
                                                                                                                      THEN /\ recordLock' = [recordLock EXCEPT ![prevLockRecord[self]] = RECORD_NOT_LOCKED]
                                                                                                                           /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = None]
                                                                                                                      ELSE /\ TRUE
                                                                                                                           /\ UNCHANGED << recordLock, 
                                                                                                                                           prevLockRecord >>
                                                                                              ELSE /\ TRUE
                                                                                                   /\ UNCHANGED << recordLock, 
                                                                                                                   prevLockRecord >>
                                                                                   ELSE /\ IF operation = OPERATION_REWRITE
                                                                                              THEN /\ lastOperation' = [lastOperation EXCEPT ![self] = OPERATION_REWRITE]
                                                                                                   /\ IF {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS} /= {}
                                                                                                         THEN /\ \E key \in {key \in keys: recordLock[key] /= RECORD_NOT_EXISTS}:
                                                                                                                   IF recordLock[key] = self \/ recordLock[key] = RECORD_NOT_LOCKED
                                                                                                                      THEN /\ TRUE
                                                                                                                           /\ IF prevLockRecord[self] /= None
                                                                                                                                 THEN /\ recordLock' = [recordLock EXCEPT ![prevLockRecord[self]] = RECORD_NOT_LOCKED]
                                                                                                                                 ELSE /\ TRUE
                                                                                                                                      /\ UNCHANGED recordLock
                                                                                                                      ELSE /\ IF prevLockRecord[self] /= None
                                                                                                                                 THEN /\ recordLock' = [recordLock EXCEPT ![prevLockRecord[self]] = RECORD_NOT_LOCKED]
                                                                                                                                 ELSE /\ TRUE
                                                                                                                                      /\ UNCHANGED recordLock
                                                                                                              /\ prevLockRecord' = [prevLockRecord EXCEPT ![self] = None]
                                                                                                         ELSE /\ TRUE
                                                                                                              /\ UNCHANGED << recordLock, 
                                                                                                                              prevLockRecord >>
                                                                                              ELSE /\ TRUE
                                                                                                   /\ UNCHANGED << recordLock, 
                                                                                                                   prevLockRecord, 
                                                                                                                   lastOperation >>
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

(* 各プログラムがすでにロックしたと'認識している'レコードは、確かにそのプログラムがロックしている *)
eachRecordWhichOneProgramThinkItIsLockedArelockedByTheProgram ==
    \A p \in programs:
        (prevLockRecord[p] /= None =>
            recordLock[prevLockRecord[p]] = p)

(* 各プログラムがすでにロックしたと'認識している'レコードは、プログラム間で重複しない *)
eachRecordWhichOneProgramThinkItIsLockedAreNotLockedByAnotherProgram ==
    \A p1, p2 \in programs:
        (p1 /= p2) =>
            (prevLockRecord[p1] = None \/ prevLockRecord[p2] = None \/ prevLockRecord[p1] /= prevLockRecord[p2])
=======================
