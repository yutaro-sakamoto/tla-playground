----------------- MODULE example ----------------
EXTENDS Integers, TLC, Sequences

(*--algorithm example

variables
    STATE_OPEN = "open",
    STATE_CLOSE = "close",
    None = 0,
    programs = 1..4,
    fileLockedBy = None
  ;

process program \in programs
variables state
begin
    OPERATE:
    while TRUE do
        if state = STATE_CLOSE then
            if fileLockedBy = None then
                fileLockedBy := self;
                state := STATE_OPEN;
            end if;
        elsif state = STATE_OPEN then
            assert fileLockedBy = self;
            fileLockedBy := None;
            state := STATE_CLOSE;
        else
            state := STATE_CLOSE;
        end if;
    end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES STATE_OPEN, STATE_CLOSE, None, programs, fileLockedBy, state

vars == << STATE_OPEN, STATE_CLOSE, None, programs, fileLockedBy, state >>

ProcSet == (programs)

Init == (* Global variables *)
        /\ STATE_OPEN = "open"
        /\ STATE_CLOSE = "close"
        /\ None = 0
        /\ programs = 1..4
        /\ fileLockedBy = None
        (* Process program *)
        /\ state = [self \in programs |-> defaultInitValue]

program(self) == /\ IF state[self] = STATE_CLOSE
                       THEN /\ IF fileLockedBy = None
                                  THEN /\ fileLockedBy' = self
                                       /\ state' = [state EXCEPT ![self] = STATE_OPEN]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << fileLockedBy, state >>
                       ELSE /\ IF state[self] = STATE_OPEN
                                  THEN /\ Assert(fileLockedBy = self, 
                                                 "Failure of assertion at line 25, column 13.")
                                       /\ fileLockedBy' = None
                                       /\ state' = [state EXCEPT ![self] = STATE_CLOSE]
                                  ELSE /\ state' = [state EXCEPT ![self] = STATE_CLOSE]
                                       /\ UNCHANGED fileLockedBy
                 /\ UNCHANGED << STATE_OPEN, STATE_CLOSE, None, programs >>

Next == (\E self \in programs: program(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=======================
