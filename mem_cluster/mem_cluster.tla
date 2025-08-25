---- MODULE mem_cluster ----
EXTENDS TLC

(*--algorithm mem_cluster

begin
  skip;
end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "77889a1c" /\ chksum(tla) = "af3d9146")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


====
