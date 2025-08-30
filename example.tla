----------------- MODULE example ----------------
EXTENDS Integers, TLC, Sequences

(*--algorithm example

variables
    STATE_OPEN = "open",
    STATE_CLOSE = "close",
    maxPrograms = 4,
    None = 0,
    programs = 1..maxPrograms,
    fileLockedBy = None
  ;

process program \in programs
variables state = STATE_CLOSE
begin
    OPERATE:
        if state = STATE_CLOSE then
            if fileLockedBy = None then
                fileLockedBy := self;
                state := STATE_OPEN;
            end if;
        else
            assert fileLockedBy = self;
            fileLockedBy := None;
            state := STATE_CLOSE;
        end if;
        goto OPERATE;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES pc, STATE_OPEN, STATE_CLOSE, maxPrograms, None, programs, 
          fileLockedBy, state

vars == << pc, STATE_OPEN, STATE_CLOSE, maxPrograms, None, programs, 
           fileLockedBy, state >>

ProcSet == (programs)

Init == (* Global variables *)
        /\ STATE_OPEN = "open"
        /\ STATE_CLOSE = "close"
        /\ maxPrograms = 4
        /\ None = 0
        /\ programs = 1..maxPrograms
        /\ fileLockedBy = None
        (* Process program *)
        /\ state = [self \in programs |-> STATE_CLOSE]
        /\ pc = [self \in ProcSet |-> "OPERATE"]

OPERATE(self) == /\ pc[self] = "OPERATE"
                 /\ IF state[self] = STATE_CLOSE
                       THEN /\ IF fileLockedBy = None
                                  THEN /\ fileLockedBy' = self
                                       /\ state' = [state EXCEPT ![self] = STATE_OPEN]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << fileLockedBy, state >>
                       ELSE /\ Assert(fileLockedBy = self, 
                                      "Failure of assertion at line 25, column 13.")
                            /\ fileLockedBy' = None
                            /\ state' = [state EXCEPT ![self] = STATE_CLOSE]
                 /\ pc' = [pc EXCEPT ![self] = "OPERATE"]
                 /\ UNCHANGED << STATE_OPEN, STATE_CLOSE, maxPrograms, None, 
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
