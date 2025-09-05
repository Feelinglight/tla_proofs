---- MODULE mem_cluster ----
EXTENDS TLC, Integers, utils, SequencesExt, FiniteSets, cluster_ops

CONSTANTS PagesCount, PageSize, ClusterSize, NULL

ASSUME PagesCount \in Nat \ {0}
ASSUME PageSize \in Nat \ {0}
ASSUME PageSize > 1

ASSUME ClusterSize \in Nat \ {0}
ASSUME ClusterSize % PageSize = 0


(*--algorithm mem_cluster
variables
  \* read only
  pages_per_half_cluster = ClusterSize \div PageSize,
  data_per_half_cluster_bytes = pages_per_half_cluster * PageSize,
  half_clusters_count = get_half_clusters_count(PagesCount, PageSize, ClusterSize),

  \* read write
  memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(0, PageSize)],
  user_buffer = SeqOfNElements(0, data_per_half_cluster_bytes),

  \* Состояния полукластеров. TRUE - последняя запись была успешна, FALSE - прервана
  \* Если в кластер еще не было ни одной записи, то состояние равно NULL
  cluster_states = [state \in 1..half_clusters_count |-> NULL],
  \* Когда в page_mem отправляется запрос на запись последней страницы полукластера,
  \* в эту переменную записывается индекс этого полукластера в cluster_states
  current_cluster_state_idx = NULL,

  \* Переменные для управления page_mem из cluster
  page_mem_current_buf_offset = 1,
  page_mem_current_page_idx = 1,
  \* Если этот флаг стоит, то запись первого байта одновременно запишет 0 в crc кластера
  page_mem_mess_crc = FALSE,
  page_mem_status = "idle";

macro update_cluster_state_idx(cluster_idx) begin
  \* Если это последняя страница в полукластере
  if user_buf_offset + PageSize >= ClusterSize then
    if next_status = "st_write_begin_2_half" then
      \* Первый полукластер в кластере
      current_cluster_state_idx := get_half_cluster_idx(cluster_idx, 1);
    else
      \* Второй полукластер в кластере
      current_cluster_state_idx := get_half_cluster_idx(cluster_idx, 2);
    end if;
  end if;
end macro;

macro validate_cluster_write(clust_idx) begin
  assert status = "st_free" =>
    /\ user_buffer = first_half_cluster_content(memory_pages, clust_idx, pages_per_half_cluster)
    /\ user_buffer = second_half_cluster_content(memory_pages, clust_idx, pages_per_half_cluster)
end macro;


macro get_crc_status() begin
  \* crc кластера считается валидной, если все элементы в нем одинаковы
  crc_1_ok := half_cluster_crc_ok(user_buffer, ClusterSize, 1);
  crc_2_ok := half_cluster_crc_ok(user_buffer, ClusterSize, 2);

  ee_crc_1_ok := user_buffer[ClusterSize] = 1;
  ee_crc_2_ok := user_buffer[ClusterSize * 2] = 1;
end macro;


fair process cluster = "Cluster"
variables
  \* read only
  clusters_count = half_clusters_count \div 2,
  allowed_values = 2..4,

  \* read write
  \* Индекс читаемого/записываемого кластера
  cluster_idx = 0,

  next_status = "st_free",
  status = "st_free";

  \* Индекс страницы для чтения/записи кластера
  page_idx = 0,
  \* Индекс в буфере данных, который пишется в кластер (или читается)
  user_buf_offset = 0,

  crc_1_ok = FALSE,
  crc_2_ok = FALSE,

  ee_crc_1_ok = FALSE,
  ee_crc_2_ok = FALSE;

begin
  ClusterTick:
    while TRUE do
      either \* Прерывание работы mem_cluster
        \* status := "st_free";
        skip;

      \* ---------- Чтение ----------
      or \* Запрос на чтение
        await status = "st_free";

        with idx \in 0..(clusters_count - 1) do
          cluster_idx := idx;
        end with;

        user_buffer := SeqOfNElements(777, 2 * data_per_half_cluster_bytes);

        status := "st_read_begin"

      or \* st_read_begin
        await status = "st_read_begin";

        page_idx := 2 * cluster_idx * pages_per_half_cluster;
        user_buf_offset := 0;

        status := "st_read_process";
      or \* st_read_process
        await status = "st_read_process" /\ page_mem_status = "idle";

        if user_buf_offset < 2 * ClusterSize then
          \* +1 - перевод в индексы с 1
          page_mem_current_buf_offset := user_buf_offset + 1;
          page_mem_current_page_idx := page_idx + 1;
          page_mem_status := "start_read";

          user_buf_offset := user_buf_offset + PageSize;
          page_idx := page_idx + 1;
        else
          status := "st_read_check_crc";
        end if;
      or \* st_read_check_crc
        await status = "st_read_check_crc";

        get_crc_status();

        with
          first_half_state = cluster_states[1 + 2 * cluster_idx],
          second_half_state = cluster_states[2 + 2 * cluster_idx]
        do
          if crc_1_ok /\ ee_crc_1_ok then

            if crc_2_ok /\ ee_crc_2_ok then
              assert first_half_state /\ second_half_state;
              status := "st_free";
            else
              assert first_half_state /\ ~second_half_state;
              \* 1 -> 2
              user_buf_offset := 0;
              page_idx := (2 * cluster_idx + 1) * pages_per_half_cluster;

              next_status := "st_free";
              status := "st_write_process";
            end if;

          else
            if crc_2_ok /\ ee_crc_2_ok then
              assert ~first_half_state /\ second_half_state;
              \* 2 -> 1
              user_buf_offset := 0;
              page_idx := 2 * cluster_idx * pages_per_half_cluster;

              next_status := "st_free";
              status := "st_write_process";
            else
              \* Если обе crc завалены, то в алгоритме ошибка и он не обеспечивает надежную запись
              \* и чтение. Исключение - оба кластера не инициализированы
              assert
                \/ crc_2_ok /\ ee_crc_2_ok
                \/ first_half_state = NULL /\ second_half_state = NULL;

              user_buffer := SeqOfNElements(Min(allowed_values), data_per_half_cluster_bytes);

              status := "st_write_begin";
            end if;
          end if;
        end with;

      \* ---------- Запись ----------
      or \* Запрос на запись
        await status = "st_free";

        with idx \in 0..(clusters_count - 1) do
          cluster_idx := idx;
        end with;

        \* TODO: исключить значения, которые уже в кластере
        with data \in allowed_values do
          user_buffer := SeqOfNElements(data, data_per_half_cluster_bytes);
        end with;

        status := "st_write_begin";

      or \* st_write_begin
        await status = "st_write_begin";
        page_idx := 2 * cluster_idx * pages_per_half_cluster;
        user_buf_offset := 0;

        \* 1 - значит crc валидна
        user_buffer[data_per_half_cluster_bytes] := 1;
        page_mem_mess_crc := TRUE;

        next_status := "st_write_begin_2_half";
        status := "st_write_process";

      or \* st_write_process
        await status = "st_write_process" /\ page_mem_status = "idle";
        update_cluster_state_idx(cluster_idx);

        if user_buf_offset < ClusterSize then
          \* +1 - перевод в индексы с 1
          page_mem_current_buf_offset := user_buf_offset + 1;
          page_mem_current_page_idx := page_idx + 1;
          page_mem_status := "start_write";

          user_buf_offset := user_buf_offset + PageSize;
          page_idx := page_idx + 1;
        else
          status := next_status;
          validate_cluster_write(cluster_idx);
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
            \* Запись первого байта кластера одновременно делает кластер и его crc невалидными
            memory_pages[page_mem_current_page_idx][1] := user_buffer[page_mem_current_buf_offset] ||
            memory_pages[crc_page][PageSize] := 0;
            if current_cluster_state_idx /= NULL then
              cluster_states[current_cluster_state_idx] := FALSE;
            end if;
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
          if current_cluster_state_idx /= NULL then
            cluster_states[current_cluster_state_idx] := TRUE;
            current_cluster_state_idx := NULL;
          end if;

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


\* BEGIN TRANSLATION (chksum(pcal) = "33698d62" /\ chksum(tla) = "e25bbe36")
VARIABLES pages_per_half_cluster, data_per_half_cluster_bytes, 
          half_clusters_count, memory_pages, user_buffer, cluster_states, 
          current_cluster_state_idx, page_mem_current_buf_offset, 
          page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, 
          clusters_count, allowed_values, cluster_idx, next_status, status, 
          page_idx, user_buf_offset, crc_1_ok, crc_2_ok, ee_crc_1_ok, 
          ee_crc_2_ok, current_byte_idx, user_buf_start_offset

vars == << pages_per_half_cluster, data_per_half_cluster_bytes, 
           half_clusters_count, memory_pages, user_buffer, cluster_states, 
           current_cluster_state_idx, page_mem_current_buf_offset, 
           page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, 
           clusters_count, allowed_values, cluster_idx, next_status, status, 
           page_idx, user_buf_offset, crc_1_ok, crc_2_ok, ee_crc_1_ok, 
           ee_crc_2_ok, current_byte_idx, user_buf_start_offset >>

ProcSet == {"Cluster"} \cup {"PageMem"}

Init == (* Global variables *)
        /\ pages_per_half_cluster = (ClusterSize \div PageSize)
        /\ data_per_half_cluster_bytes = pages_per_half_cluster * PageSize
        /\ half_clusters_count = get_half_clusters_count(PagesCount, PageSize, ClusterSize)
        /\ memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(0, PageSize)]
        /\ user_buffer = SeqOfNElements(0, data_per_half_cluster_bytes)
        /\ cluster_states = [state \in 1..half_clusters_count |-> NULL]
        /\ current_cluster_state_idx = NULL
        /\ page_mem_current_buf_offset = 1
        /\ page_mem_current_page_idx = 1
        /\ page_mem_mess_crc = FALSE
        /\ page_mem_status = "idle"
        (* Process cluster *)
        /\ clusters_count = half_clusters_count \div 2
        /\ allowed_values = 2..4
        /\ cluster_idx = 0
        /\ next_status = "st_free"
        /\ status = "st_free"
        /\ page_idx = 0
        /\ user_buf_offset = 0
        /\ crc_1_ok = FALSE
        /\ crc_2_ok = FALSE
        /\ ee_crc_1_ok = FALSE
        /\ ee_crc_2_ok = FALSE
        (* Process page_mem *)
        /\ current_byte_idx = 1
        /\ user_buf_start_offset = 1

cluster == /\ \/ /\ TRUE
                 /\ UNCHANGED <<user_buffer, current_cluster_state_idx, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, cluster_idx, next_status, status, page_idx, user_buf_offset, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ status = "st_free"
                 /\ \E idx \in 0..(clusters_count - 1):
                      cluster_idx' = idx
                 /\ user_buffer' = SeqOfNElements(777, 2 * data_per_half_cluster_bytes)
                 /\ status' = "st_read_begin"
                 /\ UNCHANGED <<current_cluster_state_idx, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, next_status, page_idx, user_buf_offset, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ status = "st_read_begin"
                 /\ page_idx' = 2 * cluster_idx * pages_per_half_cluster
                 /\ user_buf_offset' = 0
                 /\ status' = "st_read_process"
                 /\ UNCHANGED <<user_buffer, current_cluster_state_idx, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, cluster_idx, next_status, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ status = "st_read_process" /\ page_mem_status = "idle"
                 /\ IF user_buf_offset < 2 * ClusterSize
                       THEN /\ page_mem_current_buf_offset' = user_buf_offset + 1
                            /\ page_mem_current_page_idx' = page_idx + 1
                            /\ page_mem_status' = "start_read"
                            /\ user_buf_offset' = user_buf_offset + PageSize
                            /\ page_idx' = page_idx + 1
                            /\ UNCHANGED status
                       ELSE /\ status' = "st_read_check_crc"
                            /\ UNCHANGED << page_mem_current_buf_offset, 
                                            page_mem_current_page_idx, 
                                            page_mem_status, page_idx, 
                                            user_buf_offset >>
                 /\ UNCHANGED <<user_buffer, current_cluster_state_idx, page_mem_mess_crc, cluster_idx, next_status, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ status = "st_read_check_crc"
                 /\ crc_1_ok' = half_cluster_crc_ok(user_buffer, ClusterSize, 1)
                 /\ crc_2_ok' = half_cluster_crc_ok(user_buffer, ClusterSize, 2)
                 /\ ee_crc_1_ok' = (user_buffer[ClusterSize] = 1)
                 /\ ee_crc_2_ok' = (user_buffer[ClusterSize * 2] = 1)
                 /\ LET first_half_state == cluster_states[1 + 2 * cluster_idx] IN
                      LET second_half_state == cluster_states[2 + 2 * cluster_idx] IN
                        IF crc_1_ok' /\ ee_crc_1_ok'
                           THEN /\ IF crc_2_ok' /\ ee_crc_2_ok'
                                      THEN /\ Assert(first_half_state /\ second_half_state, 
                                                     "Failure of assertion at line 145, column 15.")
                                           /\ status' = "st_free"
                                           /\ UNCHANGED << next_status, 
                                                           page_idx, 
                                                           user_buf_offset >>
                                      ELSE /\ Assert(first_half_state /\ ~second_half_state, 
                                                     "Failure of assertion at line 148, column 15.")
                                           /\ user_buf_offset' = 0
                                           /\ page_idx' = (2 * cluster_idx + 1) * pages_per_half_cluster
                                           /\ next_status' = "st_free"
                                           /\ status' = "st_write_process"
                                /\ UNCHANGED user_buffer
                           ELSE /\ IF crc_2_ok' /\ ee_crc_2_ok'
                                      THEN /\ Assert(~first_half_state /\ second_half_state, 
                                                     "Failure of assertion at line 159, column 15.")
                                           /\ user_buf_offset' = 0
                                           /\ page_idx' = 2 * cluster_idx * pages_per_half_cluster
                                           /\ next_status' = "st_free"
                                           /\ status' = "st_write_process"
                                           /\ UNCHANGED user_buffer
                                      ELSE /\ Assert(\/ crc_2_ok' /\ ee_crc_2_ok'
                                                     \/ first_half_state = NULL /\ second_half_state = NULL, 
                                                     "Failure of assertion at line 169, column 15.")
                                           /\ user_buffer' = SeqOfNElements(Min(allowed_values), data_per_half_cluster_bytes)
                                           /\ status' = "st_write_begin"
                                           /\ UNCHANGED << next_status, 
                                                           page_idx, 
                                                           user_buf_offset >>
                 /\ UNCHANGED <<current_cluster_state_idx, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, cluster_idx>>
              \/ /\ status = "st_free"
                 /\ \E idx \in 0..(clusters_count - 1):
                      cluster_idx' = idx
                 /\ \E data \in allowed_values:
                      user_buffer' = SeqOfNElements(data, data_per_half_cluster_bytes)
                 /\ status' = "st_write_begin"
                 /\ UNCHANGED <<current_cluster_state_idx, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, next_status, page_idx, user_buf_offset, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ status = "st_write_begin"
                 /\ page_idx' = 2 * cluster_idx * pages_per_half_cluster
                 /\ user_buf_offset' = 0
                 /\ user_buffer' = [user_buffer EXCEPT ![data_per_half_cluster_bytes] = 1]
                 /\ page_mem_mess_crc' = TRUE
                 /\ next_status' = "st_write_begin_2_half"
                 /\ status' = "st_write_process"
                 /\ UNCHANGED <<current_cluster_state_idx, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_status, cluster_idx, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ status = "st_write_process" /\ page_mem_status = "idle"
                 /\ IF user_buf_offset + PageSize >= ClusterSize
                       THEN /\ IF next_status = "st_write_begin_2_half"
                                  THEN /\ current_cluster_state_idx' = get_half_cluster_idx(cluster_idx, 1)
                                  ELSE /\ current_cluster_state_idx' = get_half_cluster_idx(cluster_idx, 2)
                       ELSE /\ TRUE
                            /\ UNCHANGED current_cluster_state_idx
                 /\ IF user_buf_offset < ClusterSize
                       THEN /\ page_mem_current_buf_offset' = user_buf_offset + 1
                            /\ page_mem_current_page_idx' = page_idx + 1
                            /\ page_mem_status' = "start_write"
                            /\ user_buf_offset' = user_buf_offset + PageSize
                            /\ page_idx' = page_idx + 1
                            /\ UNCHANGED status
                       ELSE /\ status' = next_status
                            /\ Assert(     status' = "st_free" =>
                                      /\ user_buffer = first_half_cluster_content(memory_pages, cluster_idx, pages_per_half_cluster)
                                      /\ user_buffer = second_half_cluster_content(memory_pages, cluster_idx, pages_per_half_cluster), 
                                      "Failure of assertion at line 53, column 3 of macro called at line 221, column 11.")
                            /\ UNCHANGED << page_mem_current_buf_offset, 
                                            page_mem_current_page_idx, 
                                            page_mem_status, page_idx, 
                                            user_buf_offset >>
                 /\ UNCHANGED <<user_buffer, page_mem_mess_crc, cluster_idx, next_status, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ status = "st_write_begin_2_half"
                 /\ user_buf_offset' = 0
                 /\ page_idx' = (2 * cluster_idx + 1) * pages_per_half_cluster
                 /\ next_status' = "st_free"
                 /\ status' = "st_write_process"
                 /\ UNCHANGED <<user_buffer, current_cluster_state_idx, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, cluster_idx, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
           /\ UNCHANGED << pages_per_half_cluster, data_per_half_cluster_bytes, 
                           half_clusters_count, memory_pages, cluster_states, 
                           clusters_count, allowed_values, current_byte_idx, 
                           user_buf_start_offset >>

page_mem == /\ \/ /\ page_mem_status = "idle"
                  /\ UNCHANGED <<memory_pages, user_buffer, cluster_states, current_cluster_state_idx, page_mem_current_buf_offset, page_mem_mess_crc, page_mem_status, current_byte_idx, user_buf_start_offset>>
               \/ /\ page_mem_status = "start_read"
                  /\ user_buf_start_offset' = page_mem_current_buf_offset
                  /\ current_byte_idx' = 1
                  /\ page_mem_status' = "read"
                  /\ UNCHANGED <<memory_pages, user_buffer, cluster_states, current_cluster_state_idx, page_mem_current_buf_offset, page_mem_mess_crc>>
               \/ /\ page_mem_status = "read"
                  /\ user_buffer' = [user_buffer EXCEPT ![page_mem_current_buf_offset] = memory_pages[page_mem_current_page_idx][current_byte_idx]]
                  /\ current_byte_idx' = current_byte_idx + 1
                  /\ page_mem_current_buf_offset' = page_mem_current_buf_offset + 1
                  /\ IF current_byte_idx' > PageSize
                        THEN /\ page_mem_status' = "check_assert"
                        ELSE /\ TRUE
                             /\ UNCHANGED page_mem_status
                  /\ UNCHANGED <<memory_pages, cluster_states, current_cluster_state_idx, page_mem_mess_crc, user_buf_start_offset>>
               \/ /\ page_mem_status = "start_write"
                  /\ LET crc_page == page_mem_current_page_idx + pages_per_half_cluster - 1 IN
                       /\ IF page_mem_mess_crc
                             THEN /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx][1] = user_buffer[page_mem_current_buf_offset],
                                                                          ![crc_page][PageSize] = 0]
                                  /\ IF current_cluster_state_idx /= NULL
                                        THEN /\ cluster_states' = [cluster_states EXCEPT ![current_cluster_state_idx] = FALSE]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED cluster_states
                             ELSE /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx][1] = user_buffer[page_mem_current_buf_offset]]
                                  /\ UNCHANGED cluster_states
                       /\ page_mem_mess_crc' = FALSE
                  /\ user_buf_start_offset' = page_mem_current_buf_offset
                  /\ current_byte_idx' = 2
                  /\ page_mem_current_buf_offset' = page_mem_current_buf_offset + 1
                  /\ page_mem_status' = "write"
                  /\ UNCHANGED <<user_buffer, current_cluster_state_idx>>
               \/ /\ page_mem_status = "write"
                  /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx][current_byte_idx] = user_buffer[page_mem_current_buf_offset]]
                  /\ current_byte_idx' = current_byte_idx + 1
                  /\ page_mem_current_buf_offset' = page_mem_current_buf_offset + 1
                  /\ IF current_byte_idx' > PageSize
                        THEN /\ IF current_cluster_state_idx /= NULL
                                   THEN /\ cluster_states' = [cluster_states EXCEPT ![current_cluster_state_idx] = TRUE]
                                        /\ current_cluster_state_idx' = NULL
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << cluster_states, 
                                                        current_cluster_state_idx >>
                             /\ page_mem_status' = "check_assert"
                        ELSE /\ TRUE
                             /\ UNCHANGED << cluster_states, 
                                             current_cluster_state_idx, 
                                             page_mem_status >>
                  /\ UNCHANGED <<user_buffer, page_mem_mess_crc, user_buf_start_offset>>
               \/ /\ page_mem_status = "check_assert"
                  /\ Assert(       memory_pages[page_mem_current_page_idx] = SequencePart(
                              user_buffer, user_buf_start_offset, PageSize
                            ), "Failure of assertion at line 310, column 9.")
                  /\ page_mem_status' = "idle"
                  /\ UNCHANGED <<memory_pages, user_buffer, cluster_states, current_cluster_state_idx, page_mem_current_buf_offset, page_mem_mess_crc, current_byte_idx, user_buf_start_offset>>
            /\ UNCHANGED << pages_per_half_cluster, 
                            data_per_half_cluster_bytes, half_clusters_count, 
                            page_mem_current_page_idx, clusters_count, 
                            allowed_values, cluster_idx, next_status, status, 
                            page_idx, user_buf_offset, crc_1_ok, crc_2_ok, 
                            ee_crc_1_ok, ee_crc_2_ok >>

Next == cluster \/ page_mem

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(cluster)

\* END TRANSLATION

ClusterStatusInvariant ==
  /\  status \in {
        "st_free",
        "st_error",
        "st_read_begin",
        "st_read_process",
        "st_read_check_crc",
        "st_write_begin",
        "st_write_process",
        "st_write_begin_2_half"
      }
   /\  next_status \in {
        "st_free",
        "st_write_begin_2_half"
       }


ClusterIndexesInvariant ==
  /\ cluster_idx \in 0..(clusters_count - 1)
  /\ current_cluster_state_idx \in 1..(clusters_count * 2)
    \/ current_cluster_state_idx = NULL
  \* /\ page_idx \in 0..(PageSize - 1)
  \* /\ user_buf_offset \in 0..(2 * data_per_half_cluster_bytes)


PageMemStatusInvariant == page_mem_status \in {
  "idle",
  "start_read",
  "read",
  "start_write",
  "write",
  "check_assert"
}


PageMemIndexesInvariant ==
  /\ user_buf_start_offset \in 1..(2 * data_per_half_cluster_bytes)
  /\ page_mem_current_page_idx \in 1..PagesCount
  /\ page_mem_current_buf_offset \in 1..(2 * data_per_half_cluster_bytes + 1)
  /\ current_byte_idx \in 1..(PageSize + 1)

====

