----------------- MODULE example ----------------
EXTENDS Integers, TLC, Sequences

(*--algorithm example

variables
    STATE_OPEN = "open",
    STATE_CLOSE = "close",
    OPEN_MODE_INPUT = "input",
    OPEN_MODE_OUTPUT ="output",
    OPEN_MODE_I_O = "I-O",
    OPEN_MODE_EXTEND = "EXTEND",
    OPEN_MODE = {OPEN_MODE_INPUT, OPEN_MODE_OUTPUT, 
                 OPEN_MODE_I_O, OPEN_MODE_EXTEND},
    OPERATION_WRITE = "write",
    OPERATION_READ = "read",
    OPERATION_REWRITE = "rewrite",
    OPERATION_DELETE = "delete",
    OPERATION_CLOSE = "close",
    ALLOWED_OPERATIONS = [
        OPEN_MODE_INPUT |-> {OPERATION_READ},
        OPEN_MODE_OUTPUT |-> {OPERATION_WRITE},
        OPEN_MODE_I_O |-> {OPERATION_READ, OPERATION_REWRITE, OPERATION_DELETE},
        OPEN_MODE_EXTEND |-> {OPERATION_WRITE}
    ],
    fileLockTable = <<>>,
    maxPrograms = 4,
    None = 0,
    programs = 1..maxPrograms,
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
                    fileLockTable := Append(fileLockTable, <<self, open_mode>>);
                    state := STATE_OPEN;
                end with;
            end if;
        (* close a file*)
        else
            with operation \in {OPERATION_WRITE, OPERATION_READ, OPERATION_REWRITE, OPERATION_DELETE, OPERATION_CLOSE} do
                if operation = OPERATION_CLOSE then
                    fileLockTable := SelectSeq(fileLockTable, LAMBDA entry: entry[1] /= self);
                    recordLock := SelectSeq(recordLock, LAMBDA record: record[2] /= self);
                    state := STATE_CLOSE;
                end if
            end with;
        end if;
        goto OPERATE;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES pc, STATE_OPEN, STATE_CLOSE, OPEN_MODE_INPUT, OPEN_MODE_OUTPUT, 
          OPEN_MODE_I_O, OPEN_MODE_EXTEND, OPEN_MODE, OPERATION_WRITE, 
          OPERATION_READ, OPERATION_REWRITE, OPERATION_DELETE, 
          OPERATION_CLOSE, ALLOWED_OPERATIONS, fileLockTable, maxPrograms, 
          None, programs, recordLock

(* define statement *)
atMostOneProgramOpensOutput ==
    Len(SelectSeq(fileLockTable, LAMBDA entry: entry[2] = OPEN_MODE_OUTPUT)) <= 1

VARIABLE state

vars == << pc, STATE_OPEN, STATE_CLOSE, OPEN_MODE_INPUT, OPEN_MODE_OUTPUT, 
           OPEN_MODE_I_O, OPEN_MODE_EXTEND, OPEN_MODE, OPERATION_WRITE, 
           OPERATION_READ, OPERATION_REWRITE, OPERATION_DELETE, 
           OPERATION_CLOSE, ALLOWED_OPERATIONS, fileLockTable, maxPrograms, 
           None, programs, recordLock, state >>

ProcSet == (programs)

Init == (* Global variables *)
        /\ STATE_OPEN = "open"
        /\ STATE_CLOSE = "close"
        /\ OPEN_MODE_INPUT = "input"
        /\ OPEN_MODE_OUTPUT = "output"
        /\ OPEN_MODE_I_O = "I-O"
        /\ OPEN_MODE_EXTEND = "EXTEND"
        /\ OPEN_MODE = {OPEN_MODE_INPUT, OPEN_MODE_OUTPUT,
                        OPEN_MODE_I_O, OPEN_MODE_EXTEND}
        /\ OPERATION_WRITE = "write"
        /\ OPERATION_READ = "read"
        /\ OPERATION_REWRITE = "rewrite"
        /\ OPERATION_DELETE = "delete"
        /\ OPERATION_CLOSE = "close"
        /\ ALLOWED_OPERATIONS =                      [
                                    OPEN_MODE_INPUT |-> {OPERATION_READ},
                                    OPEN_MODE_OUTPUT |-> {OPERATION_WRITE},
                                    OPEN_MODE_I_O |-> {OPERATION_READ, OPERATION_REWRITE, OPERATION_DELETE},
                                    OPEN_MODE_EXTEND |-> {OPERATION_WRITE}
                                ]
        /\ fileLockTable = <<>>
        /\ maxPrograms = 4
        /\ None = 0
        /\ programs = 1..maxPrograms
        /\ recordLock = <<>>
        (* Process program *)
        /\ state = [self \in programs |-> STATE_CLOSE]
        /\ pc = [self \in ProcSet |-> "OPERATE"]

OPERATE(self) == /\ pc[self] = "OPERATE"
                 /\ IF state[self] = STATE_CLOSE
                       THEN /\ IF ~\E i \in 1..Len(fileLockTable): fileLockTable[i][2] = OPEN_MODE_OUTPUT
                                  THEN /\ \E open_mode \in OPEN_MODE:
                                            /\ fileLockTable' = Append(fileLockTable, <<self, open_mode>>)
                                            /\ state' = [state EXCEPT ![self] = STATE_OPEN]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << fileLockTable, state >>
                            /\ UNCHANGED recordLock
                       ELSE /\ \E operation \in {OPERATION_WRITE, OPERATION_READ, OPERATION_REWRITE, OPERATION_DELETE, OPERATION_CLOSE}:
                                 IF operation = OPERATION_CLOSE
                                    THEN /\ fileLockTable' = SelectSeq(fileLockTable, LAMBDA entry: entry[1] /= self)
                                         /\ recordLock' = SelectSeq(recordLock, LAMBDA record: record[2] /= self)
                                         /\ state' = [state EXCEPT ![self] = STATE_CLOSE]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << fileLockTable, 
                                                         recordLock, state >>
                 /\ pc' = [pc EXCEPT ![self] = "OPERATE"]
                 /\ UNCHANGED << STATE_OPEN, STATE_CLOSE, OPEN_MODE_INPUT, 
                                 OPEN_MODE_OUTPUT, OPEN_MODE_I_O, 
                                 OPEN_MODE_EXTEND, OPEN_MODE, OPERATION_WRITE, 
                                 OPERATION_READ, OPERATION_REWRITE, 
                                 OPERATION_DELETE, OPERATION_CLOSE, 
                                 ALLOWED_OPERATIONS, maxPrograms, None, 
                                 programs >>

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
