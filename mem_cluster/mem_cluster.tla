---- MODULE mem_cluster ----
EXTENDS TLC, Integers

CONSTANTS PagesCount, PageSize, ClusterSizePages

ASSUME PagesCount \in Nat \ {0}
ASSUME PageSize \in Nat \ {0}
ASSUME ClusterSizePages \in Nat \ {0}
ASSUME PagesCount % ClusterSizePages = 0

SeqOfNElements(element, n) == [x \in 1..n |-> element]

(*--algorithm mem_cluster

variables
  half_cluster_size_pages = ClusterSizePages \div 2,
  memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(0, PageSize)];

begin

print(memory_pages)
end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "143c28ab" /\ chksum(tla) = "ba11843c")
VARIABLES pc, half_cluster_size_pages, memory_pages

vars == << pc, half_cluster_size_pages, memory_pages >>

Init == (* Global variables *)
        /\ half_cluster_size_pages = (ClusterSizePages \div 2)
        /\ memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(0, PageSize)]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ PrintT((memory_pages))
         /\ pc' = "Done"
         /\ UNCHANGED << half_cluster_size_pages, memory_pages >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


====
