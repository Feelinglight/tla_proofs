---- MODULE mem_cluster ----
EXTENDS TLC, Integers, utils

CONSTANTS PagesCount, PageSize, ClusterSize

ASSUME PagesCount \in Nat \ {0}
ASSUME PageSize \in Nat \ {0}
ASSUME PageSize > 1

ASSUME ClusterSize \in Nat \ {0}
ASSUME ClusterSize % PageSize = 0


(*--algorithm mem_cluster
variables
  \* read only
  pages_per_half_cluster = ClusterSize \div PageSize,
  pages_per_full_cluster = pages_per_half_cluster * 2,
  data_per_cluster_bytes = pages_per_half_cluster * PageSize,

  \* read write
  memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(0, PageSize)],
  user_buffer = SeqOfNElements(0, data_per_cluster_bytes),

  page_mem_current_buf_offset = 0,
  page_mem_current_page_idx = 0,
  \* Если этот флаг стоит, то запись первого байта одновременно запишет 0 в crc кластера
  page_mem_mess_crc = FALSE,
  page_mem_status = "idle";

fair process cluster = "Cluster"
variables
  \* read only
  clusters_count = PagesCount \div (pages_per_half_cluster * 2),
  allowed_values = 2..4,

  \* read write
  \* Индекс читаемого/записываемого кластера
  cluster_idx = 0,

  next_status = "st_free",
  status = "st_free";

  \* Индекс страницы для чтения/записи кластера
  page_idx = 0,
  \* Индекс в буфере данных, который пишется в кластер
  user_buf_offset = 0,


begin
  ClusterTick:
    while TRUE do
      either \* Прерывание работы mem_cluster
        \* status := "st_free";
        skip;

      \* ---------- Чтение ----------
      or \* Запрос на чтение
        await status = "st_free";

        with idx \in 1..clusters_count do
          cluster_idx := idx;
        end with;

        user_buffer := SeqOfNElements(0, data_per_cluster_bytes);

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

        with idx \in 0..(clusters_count - 1) do
          cluster_idx := idx;
        end with;

        with data \in allowed_values do
          user_buffer := SeqOfNElements(data, data_per_cluster_bytes);
        end with;

        status := "st_write_begin";

      or \* st_write_begin
        await status = "st_write_begin";
        page_idx := 2 * cluster_idx * pages_per_half_cluster;
        user_buf_offset := 0;

        \* 1 - значит crc валидна
        user_buffer[data_per_cluster_bytes] := 1;
        page_mem_mess_crc := TRUE;

        next_status := "st_write_begin_2_half";
        status := "st_write_process";

      or \* st_write_process
        await status = "st_write_process" /\ page_mem_status = "idle";

        if user_buf_offset < ClusterSize then
          \* +1 - перевод в индексы с 1
          page_mem_current_buf_offset := user_buf_offset + 1;
          page_mem_current_page_idx := page_idx + 1;
          page_mem_status := "start_write";

          user_buf_offset := user_buf_offset + PageSize;
          page_idx := page_idx + 1;
        else
          status := next_status;

          print("========");
          print(next_status);
          print(memory_pages);
          print(cluster_idx);
          print(user_buffer);
          print(
            FlatSubSequences(
              SequencePart(
                memory_pages, 2 * cluster_idx * pages_per_half_cluster + 1, pages_per_half_cluster * 2
              )
            )
          );

          assert status = "st_free" =>
            /\  user_buffer = FlatSubSequences(
                  SequencePart(
                    memory_pages,
                    2 * cluster_idx * pages_per_half_cluster + 1,
                    pages_per_half_cluster
                  )
                )
            /\  user_buffer = FlatSubSequences(
                  SequencePart(
                    memory_pages,
                    (2 * cluster_idx + 1) * pages_per_half_cluster + 1,
                    pages_per_half_cluster
                  )
                )

        end if;
      or \* st_write_begin_2_half
        await status = "st_write_begin_2_half";
        user_buf_offset := 0;
        page_idx := (2 * cluster_idx + 1) * pages_per_half_cluster;

        next_status := "st_free";
        status := "st_write_process";
      end either;
    end while;
end process;

process page_mem = "PageMem"
variables
  current_byte_idx = 1;
  \* Нужен только для ассертов
  user_buf_start_offset = 1;

begin
  PageMemTick:
    while TRUE do
      either \* idle
        await page_mem_status = "idle";

      \* ---------- Чтение ----------
      or \* start_read
        await page_mem_status = "start_read";

        user_buf_start_offset := page_mem_current_buf_offset;
        current_byte_idx := 1;

        page_mem_status := "read";

      or \* read
        await page_mem_status = "read";

        user_buffer[page_mem_current_buf_offset] :=
          memory_pages[page_mem_current_page_idx][current_byte_idx];
        current_byte_idx := current_byte_idx + 1;
        page_mem_current_buf_offset := page_mem_current_buf_offset + 1;

        if current_byte_idx > PageSize then
          page_mem_status := "check_assert";
        end if;

      \* ---------- Запись ----------
      or \* start_write
        await page_mem_status = "start_write";

        with crc_page = page_mem_current_page_idx + pages_per_half_cluster - 1 do
          if page_mem_mess_crc then
            \* Запись первого байта кластера одновременно делает crc невалидной
            memory_pages[page_mem_current_page_idx][1] := user_buffer[page_mem_current_buf_offset] ||
            memory_pages[crc_page][PageSize] := 0;
          else
            memory_pages[page_mem_current_page_idx][1] := user_buffer[page_mem_current_buf_offset];
          end if;
          page_mem_mess_crc := FALSE;
        end with;

        user_buf_start_offset := page_mem_current_buf_offset;
        current_byte_idx := 2;
        page_mem_current_buf_offset := page_mem_current_buf_offset + 1;

        page_mem_status := "write";
      or \* write
        await page_mem_status = "write";

        memory_pages[page_mem_current_page_idx][current_byte_idx] :=
          user_buffer[page_mem_current_buf_offset];
        current_byte_idx := current_byte_idx + 1;
        page_mem_current_buf_offset := page_mem_current_buf_offset + 1;

        if current_byte_idx > PageSize then
          page_mem_status := "check_assert";
        end if;

      \* ---------- Assert ----------
      or
        await page_mem_status = "check_assert";
        assert memory_pages[page_mem_current_page_idx] = SequencePart(
          user_buffer, user_buf_start_offset, PageSize
        );
        page_mem_status := "idle";
      end either;
    end while;
end process;

end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "6d0a74fe" /\ chksum(tla) = "fd5d7720")
VARIABLES pages_per_half_cluster, pages_per_full_cluster, 
          data_per_cluster_bytes, memory_pages, user_buffer, 
          page_mem_current_buf_offset, page_mem_current_page_idx, 
          page_mem_mess_crc, page_mem_status, clusters_count, allowed_values, 
          cluster_idx, next_status, status, page_idx, user_buf_offset, 
          current_byte_idx, user_buf_start_offset

vars == << pages_per_half_cluster, pages_per_full_cluster, 
           data_per_cluster_bytes, memory_pages, user_buffer, 
           page_mem_current_buf_offset, page_mem_current_page_idx, 
           page_mem_mess_crc, page_mem_status, clusters_count, allowed_values, 
           cluster_idx, next_status, status, page_idx, user_buf_offset, 
           current_byte_idx, user_buf_start_offset >>

ProcSet == {"Cluster"} \cup {"PageMem"}

Init == (* Global variables *)
        /\ pages_per_half_cluster = (ClusterSize \div PageSize)
        /\ pages_per_full_cluster = pages_per_half_cluster * 2
        /\ data_per_cluster_bytes = pages_per_half_cluster * PageSize
        /\ memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(0, PageSize)]
        /\ user_buffer = SeqOfNElements(0, data_per_cluster_bytes)
        /\ page_mem_current_buf_offset = 0
        /\ page_mem_current_page_idx = 0
        /\ page_mem_mess_crc = FALSE
        /\ page_mem_status = "idle"
        (* Process cluster *)
        /\ clusters_count = PagesCount \div (pages_per_half_cluster * 2)
        /\ allowed_values = 2..4
        /\ cluster_idx = 0
        /\ next_status = "st_free"
        /\ status = "st_free"
        /\ page_idx = 0
        /\ user_buf_offset = 0
        (* Process page_mem *)
        /\ current_byte_idx = 1
        /\ user_buf_start_offset = 1

cluster == /\ \/ /\ TRUE
                 /\ UNCHANGED <<user_buffer, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, cluster_idx, next_status, status, page_idx, user_buf_offset>>
              \/ /\ status = "st_free"
                 /\ \E idx \in 1..clusters_count:
                      cluster_idx' = idx
                 /\ user_buffer' = SeqOfNElements(0, data_per_cluster_bytes)
                 /\ status' = "st_read_begin"
                 /\ UNCHANGED <<page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, next_status, page_idx, user_buf_offset>>
              \/ /\ status = "st_read_begin"
                 /\ UNCHANGED <<user_buffer, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, cluster_idx, next_status, status, page_idx, user_buf_offset>>
              \/ /\ status = "st_read_process"
                 /\ UNCHANGED <<user_buffer, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, cluster_idx, next_status, status, page_idx, user_buf_offset>>
              \/ /\ status = "st_read_check_crc"
                 /\ UNCHANGED <<user_buffer, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, cluster_idx, next_status, status, page_idx, user_buf_offset>>
              \/ /\ status = "st_free"
                 /\ \E idx \in 0..(clusters_count - 1):
                      cluster_idx' = idx
                 /\ \E data \in allowed_values:
                      user_buffer' = SeqOfNElements(data, data_per_cluster_bytes)
                 /\ status' = "st_write_begin"
                 /\ UNCHANGED <<page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, next_status, page_idx, user_buf_offset>>
              \/ /\ status = "st_write_begin"
                 /\ page_idx' = 2 * cluster_idx * pages_per_half_cluster
                 /\ user_buf_offset' = 0
                 /\ user_buffer' = [user_buffer EXCEPT ![data_per_cluster_bytes] = 1]
                 /\ page_mem_mess_crc' = TRUE
                 /\ next_status' = "st_write_begin_2_half"
                 /\ status' = "st_write_process"
                 /\ UNCHANGED <<page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_status, cluster_idx>>
              \/ /\ status = "st_write_process" /\ page_mem_status = "idle"
                 /\ IF user_buf_offset < ClusterSize
                       THEN /\ page_mem_current_buf_offset' = user_buf_offset + 1
                            /\ page_mem_current_page_idx' = page_idx + 1
                            /\ page_mem_status' = "start_write"
                            /\ user_buf_offset' = user_buf_offset + PageSize
                            /\ page_idx' = page_idx + 1
                            /\ UNCHANGED status
                       ELSE /\ status' = next_status
                            /\ PrintT(("========"))
                            /\ PrintT((next_status))
                            /\ PrintT((memory_pages))
                            /\ PrintT((cluster_idx))
                            /\ PrintT((user_buffer))
                            /\ PrintT(     (
                                        FlatSubSequences(
                                          SequencePart(
                                            memory_pages, 2 * cluster_idx * pages_per_half_cluster + 1, pages_per_half_cluster * 2
                                          )
                                        )
                                      ))
                            /\ Assert(     status' = "st_free" =>
                                      /\  user_buffer = FlatSubSequences(
                                            SequencePart(
                                              memory_pages,
                                              2 * cluster_idx * pages_per_half_cluster + 1,
                                              pages_per_half_cluster
                                            )
                                          )
                                      /\  user_buffer = FlatSubSequences(
                                            SequencePart(
                                              memory_pages,
                                              (2 * cluster_idx + 1) * pages_per_half_cluster + 1,
                                              pages_per_half_cluster
                                            )
                                          ), 
                                      "Failure of assertion at line 129, column 11.")
                            /\ UNCHANGED << page_mem_current_buf_offset, 
                                            page_mem_current_page_idx, 
                                            page_mem_status, page_idx, 
                                            user_buf_offset >>
                 /\ UNCHANGED <<user_buffer, page_mem_mess_crc, cluster_idx, next_status>>
              \/ /\ status = "st_write_begin_2_half"
                 /\ user_buf_offset' = 0
                 /\ page_idx' = (2 * cluster_idx + 1) * pages_per_half_cluster
                 /\ next_status' = "st_free"
                 /\ status' = "st_write_process"
                 /\ UNCHANGED <<user_buffer, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, cluster_idx>>
           /\ UNCHANGED << pages_per_half_cluster, pages_per_full_cluster, 
                           data_per_cluster_bytes, memory_pages, 
                           clusters_count, allowed_values, current_byte_idx, 
                           user_buf_start_offset >>

page_mem == /\ \/ /\ page_mem_status = "idle"
                  /\ UNCHANGED <<memory_pages, user_buffer, page_mem_current_buf_offset, page_mem_mess_crc, page_mem_status, current_byte_idx, user_buf_start_offset>>
               \/ /\ page_mem_status = "start_read"
                  /\ user_buf_start_offset' = page_mem_current_buf_offset
                  /\ current_byte_idx' = 1
                  /\ page_mem_status' = "read"
                  /\ UNCHANGED <<memory_pages, user_buffer, page_mem_current_buf_offset, page_mem_mess_crc>>
               \/ /\ page_mem_status = "read"
                  /\ user_buffer' = [user_buffer EXCEPT ![page_mem_current_buf_offset] = memory_pages[page_mem_current_page_idx][current_byte_idx]]
                  /\ current_byte_idx' = current_byte_idx + 1
                  /\ page_mem_current_buf_offset' = page_mem_current_buf_offset + 1
                  /\ IF current_byte_idx' > PageSize
                        THEN /\ page_mem_status' = "check_assert"
                        ELSE /\ TRUE
                             /\ UNCHANGED page_mem_status
                  /\ UNCHANGED <<memory_pages, page_mem_mess_crc, user_buf_start_offset>>
               \/ /\ page_mem_status = "start_write"
                  /\ LET crc_page == page_mem_current_page_idx + pages_per_half_cluster - 1 IN
                       /\ IF page_mem_mess_crc
                             THEN /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx][1] = user_buffer[page_mem_current_buf_offset],
                                                                          ![crc_page][PageSize] = 0]
                             ELSE /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx][1] = user_buffer[page_mem_current_buf_offset]]
                       /\ page_mem_mess_crc' = FALSE
                  /\ user_buf_start_offset' = page_mem_current_buf_offset
                  /\ current_byte_idx' = 2
                  /\ page_mem_current_buf_offset' = page_mem_current_buf_offset + 1
                  /\ page_mem_status' = "write"
                  /\ UNCHANGED user_buffer
               \/ /\ page_mem_status = "write"
                  /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx][current_byte_idx] = user_buffer[page_mem_current_buf_offset]]
                  /\ current_byte_idx' = current_byte_idx + 1
                  /\ page_mem_current_buf_offset' = page_mem_current_buf_offset + 1
                  /\ IF current_byte_idx' > PageSize
                        THEN /\ page_mem_status' = "check_assert"
                        ELSE /\ TRUE
                             /\ UNCHANGED page_mem_status
                  /\ UNCHANGED <<user_buffer, page_mem_mess_crc, user_buf_start_offset>>
               \/ /\ page_mem_status = "check_assert"
                  /\ Assert(       memory_pages[page_mem_current_page_idx] = SequencePart(
                              user_buffer, user_buf_start_offset, PageSize
                            ), "Failure of assertion at line 225, column 9.")
                  /\ page_mem_status' = "idle"
                  /\ UNCHANGED <<memory_pages, user_buffer, page_mem_current_buf_offset, page_mem_mess_crc, current_byte_idx, user_buf_start_offset>>
            /\ UNCHANGED << pages_per_half_cluster, pages_per_full_cluster, 
                            data_per_cluster_bytes, page_mem_current_page_idx, 
                            clusters_count, allowed_values, cluster_idx, 
                            next_status, status, page_idx, user_buf_offset >>

Next == cluster \/ page_mem

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(cluster)

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
  /\ page_mem_status \in {
      "free",
      "read",
      "write",
      "write_remains",
      "check_assert"
    }

====
