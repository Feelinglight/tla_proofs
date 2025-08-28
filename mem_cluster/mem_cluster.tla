---- MODULE mem_cluster ----
EXTENDS TLC, Integers

CONSTANTS PagesCount, PageSize, ClusterSize

ASSUME PagesCount \in Nat \ {0}
ASSUME PageSize \in Nat \ {0}
ASSUME ClusterSize \in Nat \ {0}

SeqOfNElements(element, n) == [x \in 1..n |-> element]

(*--algorithm mem_cluster

variables
  \* read only
  pages_per_half_cluster = ClusterSize \div PageSize,
  \* Последний элемент в полукластере - crc
  data_per_cluster_bytes = pages_per_half_cluster * PageSize - 1,
  clusters_count = PagesCount \div (pages_per_half_cluster * 2),

  \* read write
  memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(0, PageSize)],
  read_buffer = SeqOfNElements(0, data_per_cluster_bytes),
  cluster_idx = 1,

  status = "st_free";

begin
  P:
  print(clusters_count);
  Tick:
    while TRUE do
      either \* Прерывание работы mem_cluster
        status := "st_free";

      \* ---------- Чтение ----------
      or \* Запрос на чтение
        await status = "st_free";

        with idx \in 1..clusters_count do
          cluster_idx := idx;
        end with;

        read_buffer := SeqOfNElements(0, data_per_cluster_bytes);

        status := "st_read_begin"

      or \* st_read_begin
        await status = "st_read_begin";
      or \* st_read_process
        await status = "st_read_process";
      or \* st_read_check_crc
        await status = "st_read_check_crc";

      \* ---------- Запись ----------
      or \* Запрос на запись
        await status = "st_free";

        with idx \in 1..clusters_count do
          cluster_idx := idx;
        end with;

        with data \in 2..4 do
          read_buffer := SeqOfNElements(data, data_per_cluster_bytes);
        end with;

        status := "st_write_begin";

      or \* st_write_begin
        await status = "st_write_begin";
      or \* st_write_process
        await status = "st_write_process";
      or \* st_write_begin_2_half
        await status = "st_write_begin_2_half";
      end either;
end while;

print(memory_pages)
end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "525e7c79" /\ chksum(tla) = "9bc31187")
VARIABLES pc, pages_per_half_cluster, data_per_cluster_bytes, clusters_count, 
          memory_pages, read_buffer, cluster_idx, status

vars == << pc, pages_per_half_cluster, data_per_cluster_bytes, clusters_count, 
           memory_pages, read_buffer, cluster_idx, status >>

Init == (* Global variables *)
        /\ pages_per_half_cluster = (ClusterSize \div PageSize)
        /\ data_per_cluster_bytes = pages_per_half_cluster * PageSize - 1
        /\ clusters_count = (PagesCount \div (pages_per_half_cluster * 2))
        /\ memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(0, PageSize)]
        /\ read_buffer = SeqOfNElements(0, data_per_cluster_bytes)
        /\ cluster_idx = 1
        /\ status = "st_free"
        /\ pc = "P"

P == /\ pc = "P"
     /\ PrintT((clusters_count))
     /\ pc' = "Tick"
     /\ UNCHANGED << pages_per_half_cluster, data_per_cluster_bytes, 
                     clusters_count, memory_pages, read_buffer, cluster_idx, 
                     status >>

Tick == /\ pc = "Tick"
        /\ \/ /\ status' = "st_free"
              /\ UNCHANGED <<read_buffer, cluster_idx>>
           \/ /\ status = "st_free"
              /\ \E idx \in 1..clusters_count:
                   cluster_idx' = idx
              /\ read_buffer' = SeqOfNElements(0, data_per_cluster_bytes)
              /\ status' = "st_read_begin"
           \/ /\ status = "st_read_begin"
              /\ UNCHANGED <<read_buffer, cluster_idx, status>>
           \/ /\ status = "st_read_process"
              /\ UNCHANGED <<read_buffer, cluster_idx, status>>
           \/ /\ status = "st_read_check_crc"
              /\ UNCHANGED <<read_buffer, cluster_idx, status>>
           \/ /\ status = "st_free"
              /\ \E idx \in 1..clusters_count:
                   cluster_idx' = idx
              /\ \E data \in 2..4:
                   read_buffer' = SeqOfNElements(data, data_per_cluster_bytes)
              /\ status' = "st_write_begin"
           \/ /\ status = "st_write_begin"
              /\ UNCHANGED <<read_buffer, cluster_idx, status>>
           \/ /\ status = "st_write_process"
              /\ UNCHANGED <<read_buffer, cluster_idx, status>>
           \/ /\ status = "st_write_begin_2_half"
              /\ UNCHANGED <<read_buffer, cluster_idx, status>>
        /\ pc' = "Tick"
        /\ UNCHANGED << pages_per_half_cluster, data_per_cluster_bytes, 
                        clusters_count, memory_pages >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == P \/ Tick
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

TypeInvariant ==
  /\ status \in {
      "st_free",
      "st_error",
      "st_read_begin",
      "st_read_process",
      "st_read_check_crc",
      "st_write_begin",
      "st_write_process",
      "st_write_begin_2_hal"
    }
  /\ cluster_idx \in 1..clusters_count

====
