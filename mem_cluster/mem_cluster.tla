---- MODULE mem_cluster ----
EXTENDS TLC, Integers, utils, SequencesExt, FiniteSets, cluster_ops

CONSTANTS PagesCount, PageSize, ClusterSize, NULL, INIT_MEM_VALUE, ALLOWED_MEM_VALUES

ASSUME PagesCount \in Nat \ {0}
ASSUME PageSize \in Nat \ {0}
ASSUME PageSize > 1

ASSUME ClusterSize \in Nat \ {0}
ASSUME ClusterSize % PageSize = 0

\* 0 и 1 используются под состояние чексуммы
ASSUME INIT_MEM_VALUE \in Nat \ {0}
ASSUME ALLOWED_MEM_VALUES \subseteq (Nat \ {0, 1})


(*--algorithm mem_cluster
variables
  \* read only
  pages_per_half_cluster = ClusterSize \div PageSize,
  half_clusters_count = get_half_clusters_count(PagesCount, PageSize, ClusterSize),
  clusters_count = half_clusters_count \div 2,

  \* read write
  memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)],
  user_buffer = SeqOfNElements(INIT_MEM_VALUE, ClusterSize),

  client_init = TRUE,
  \* Индекс читаемого/записываемого кластера
  cluster_idx = 0,
  cluster_status = "st_free",

  \* Состояния полукластеров. TRUE - последняя запись была успешна, FALSE - прервана
  \* Если в кластер еще не было ни одной записи, то состояние равно NULL
  cluster_states = [state \in 1..half_clusters_count |-> NULL],
  \* Половина кластера, которая записывается в данный момент. 1 или 2
  current_write_half = 1,
  \* Когда в page_mem отправляется запрос на запись последней страницы полукластера,
  \* в эту переменную записывается индекс этого полукластера в cluster_states
  current_cluster_state_idx = NULL,

  \* Переменные для управления page_mem из cluster
  page_mem_current_buf_offset = 1,
  page_mem_current_page_idx = 1,
  \* Если этот флаг стоит, то запись первого байта одновременно запишет 0 в crc кластера
  page_mem_mess_crc = FALSE,
  page_mem_status = "idle";



macro validate_cluster_write(clust_idx) begin
  assert cluster_status = "st_free" =>
    /\ user_buffer = first_half_cluster_content(memory_pages, clust_idx, pages_per_half_cluster)
    /\ user_buffer = second_half_cluster_content(memory_pages, clust_idx, pages_per_half_cluster)
end macro;

macro prepare_write_process(cluster_idx, half_cluster_idx) begin
  assert half_cluster_idx \in {1, 2};

  user_buf_offset := 0;
  page_idx := get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, half_cluster_idx);
  page_mem_mess_crc := TRUE;
  current_cluster_state_idx := get_half_cluster_idx(cluster_idx, half_cluster_idx);
  current_write_half := half_cluster_idx;
end macro;

macro get_crc_status() begin
  \* crc кластера считается валидной, если все элементы в нем одинаковы
  crc_1_ok := half_cluster_crc_ok(user_buffer, ClusterSize, 1);
  crc_2_ok := half_cluster_crc_ok(user_buffer, ClusterSize, 2);

  ee_crc_1_ok := user_buffer[ClusterSize] = 1;
  ee_crc_2_ok := user_buffer[ClusterSize * 2] = 1;
end macro;

macro validate_page_mem_op() begin
  assert memory_pages[page_mem_current_page_idx] = SequencePart(
    user_buffer, page_mem_current_buf_offset, PageSize
  );
end macro;

\* Обновляет состояние кластера
macro set_half_cluster_state(state) begin
  if current_cluster_state_idx /= NULL then
    if ~state /\ cluster_states[current_cluster_state_idx] = NULL then
      \* Неинициализированные кластеры не нужно переводить в состояние FALSE
      skip;
    else
      cluster_states[current_cluster_state_idx] := state;
    end if;
    if pages_per_half_cluster > 1 then
      \* Если полукластер влазит в одну страницу, то подпись записывается в нее
      current_cluster_state_idx := NULL;
    end if;
  end if;
end macro;

fair process reset = "Reset"
begin
  ResetTick:
    while TRUE do
      either
        cluster_status := "st_init";
        page_mem_status := "init";
        client_init := TRUE;
      or
        skip;
      end either;
    end while;
end process;

fair process client = "Client"
variables
  client_init_queue = <<>>;
begin
  ResetTick:
    while TRUE do
      if client_init then
        client_init := FALSE;
        client_init_queue := [x \in 1..clusters_count |-> (x - 1)];
      else
        either
          await Len(client_init_queue) /= 0 /\ cluster_status = "st_free";
          cluster_idx := Head(client_init_queue);
          client_init_queue := Tail(client_init_queue);
          user_buffer := SeqOfNElements(INIT_MEM_VALUE, 2 * ClusterSize);
          cluster_status := "st_read_begin";
        or
          await Len(client_init_queue) = 0 /\ cluster_status = "st_free";

          with idx \in 0..(clusters_count - 1) do
            cluster_idx := idx;
          end with;

          user_buffer := SeqOfNElements(INIT_MEM_VALUE, 2 * ClusterSize);
          cluster_status := "st_read_begin"
        or
          await Len(client_init_queue) = 0 /\ cluster_status = "st_free";

          with idx \in 0..(clusters_count - 1) do
            cluster_idx := idx;
          end with;

          \* TODO: исключить значения, которые уже в кластере
          with data \in ALLOWED_MEM_VALUES do
            user_buffer := SeqOfNElements(data, ClusterSize);
          end with;
          cluster_status := "st_write_begin";

        end either;
      end if;
    end while;
end process;

fair process cluster = "Cluster"
variables
  \* read write

  next_status = "st_free",

  \* Индекс текущей страницы для чтения/записи кластера
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
        await cluster_status = "st_init";
        cluster_status := "st_free";

      \* ---------- Чтение ----------
      or \* st_read_begin
        await cluster_status = "st_read_begin";

        page_idx := get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, 1);
        user_buf_offset := 0;

        cluster_status := "st_read_process";
      or \* st_read_process
        await cluster_status = "st_read_process" /\ page_mem_status = "idle";

        if user_buf_offset < 2 * ClusterSize then
          \* +1 - перевод в индексы с 1
          page_mem_current_buf_offset := user_buf_offset + 1;
          page_mem_current_page_idx := page_idx + 1;
          page_mem_status := "start_read";

          user_buf_offset := user_buf_offset + PageSize;
          page_idx := page_idx + 1;
          \* NOTE: Можно проверять что страница считалась правильно

        else
          assert user_buffer = full_cluster_content(
            memory_pages, cluster_idx, pages_per_half_cluster
          );
          cluster_status := "st_read_check_crc";
        end if;
      or \* st_read_check_crc
        await cluster_status = "st_read_check_crc";

        get_crc_status();

        with
          first_half_state = cluster_states[get_half_cluster_idx(cluster_idx, 1)],
          second_half_state = cluster_states[get_half_cluster_idx(cluster_idx, 2)]
        do
          if crc_1_ok /\ ee_crc_1_ok then
            assert first_half_state;

            if crc_2_ok /\ ee_crc_2_ok then
              assert second_half_state;
              \* Все ок
              cluster_status := "st_free";
            else
              assert
                /\ second_half_state \in {NULL, FALSE}
                /\ ~half_clusters_equal(user_buffer, ClusterSize);

              \* Копируем 1 -> 2
              user_buffer := SequencePart(user_buffer, 1, ClusterSize);
              prepare_write_process(cluster_idx, 2);

              next_status := "st_free";
              cluster_status := "st_write_process";
            end if;

          else
            if crc_2_ok /\ ee_crc_2_ok then
              assert
                /\ first_half_state /= NULL
                /\ ~first_half_state /\ second_half_state
                /\ ~half_clusters_equal(user_buffer, ClusterSize);

              \* Копируем 2 -> 1
              user_buffer := SequencePart(user_buffer, ClusterSize + 1, ClusterSize);
              prepare_write_process(cluster_idx, 1);

              next_status := "st_free";
              cluster_status := "st_write_process";
            else
              \* Если обе crc завалены, то либо оба кластера не инициализированы, либо только второй
              \* (первый мог быть инициализирован, а при повторной записи возникло прервание),
              \* либо алгоритме ошибка и он не обеспечивает надежную запись
              assert second_half_state = NULL;

              user_buffer := SeqOfNElements(Min(ALLOWED_MEM_VALUES), ClusterSize);

              cluster_status := "st_write_begin";
            end if;
          end if;
        end with;

      \* ---------- Запись ----------
      or \* st_write_begin
        await cluster_status = "st_write_begin";

        prepare_write_process(cluster_idx, 1);
        \* 1 - значит crc валидна
        user_buffer[ClusterSize] := 1;

        next_status := "st_write_begin_2_half";
        cluster_status := "st_write_process";

      or \* st_write_process
        await cluster_status = "st_write_process" /\ page_mem_status = "idle";
        if user_buf_offset + PageSize >= ClusterSize then
          \* Если это последняя страница в полукластере
          current_cluster_state_idx := get_half_cluster_idx(cluster_idx, current_write_half);
        end if;

        if user_buf_offset < ClusterSize then
          \* +1 - перевод в индексы с 1
          page_mem_current_buf_offset := user_buf_offset + 1;
          page_mem_current_page_idx := page_idx + 1;
          page_mem_status := "start_write";

          user_buf_offset := user_buf_offset + PageSize;
          page_idx := page_idx + 1;
          \* NOTE: Можно проверять что страница записалась правильно
        else
          cluster_status := next_status;
          validate_cluster_write(cluster_idx);
          \* NOTE: Можно проверять что отдельные полукластеры записались правильно
          \* NOTE: Можно проверять вычисляемая и записанная crc валидны
        end if;
      or \* st_write_begin_2_half
        await cluster_status = "st_write_begin_2_half";

        prepare_write_process(cluster_idx, 2);

        next_status := "st_free";
        cluster_status := "st_write_process";
      end either;
    end while;
end process;

process page_mem = "PageMem"
begin
  PageMemTick:
    while TRUE do
      either \* init
        await page_mem_status = "init";

        page_mem_status := "idle";

      or \* idle
        await page_mem_status = "idle";

      \* ---------- Чтение ----------
      or \* start_read
        await page_mem_status = "start_read";

        user_buffer[page_mem_current_buf_offset] := memory_pages[page_mem_current_page_idx][1];

        page_mem_status := "read_tail";

      or \* read_tail
        await page_mem_status = "read_tail";

        with first_user_buf_part_size = page_mem_current_buf_offset + PageSize do
          user_buffer := SequencePart(user_buffer, 1, page_mem_current_buf_offset) \o
            SequencePart(memory_pages[page_mem_current_page_idx], 2, PageSize - 1) \o
            SequencePart(
              user_buffer, first_user_buf_part_size, Len(user_buffer) - first_user_buf_part_size + 1
            );
        end with;

        assert Len(user_buffer) = ClusterSize * 2;
        validate_page_mem_op();
        page_mem_status := "idle";

      \* ---------- Запись ----------
      or \* start_write
        await page_mem_status = "start_write";

        with crc_page = page_mem_current_page_idx + pages_per_half_cluster - 1 do
          if page_mem_mess_crc then
            \* Запись первого байта кластера одновременно делает кластер и его crc невалидными
            memory_pages[page_mem_current_page_idx][1] := user_buffer[page_mem_current_buf_offset] ||
            memory_pages[crc_page][PageSize] := 0;
            \* Кластер считается невалидным после записи первого байта в первую страницу
            set_half_cluster_state(FALSE);
          else
            memory_pages[page_mem_current_page_idx][1] := user_buffer[page_mem_current_buf_offset];
          end if;

          page_mem_mess_crc := FALSE;
        end with;

        page_mem_status := "write_middle";
      or \* write_middle
        await page_mem_status = "write_middle";

        memory_pages[page_mem_current_page_idx] := <<user_buffer[page_mem_current_buf_offset]>> \o
          SequencePart(user_buffer, page_mem_current_buf_offset + 1, PageSize - 2) \o
          <<memory_pages[page_mem_current_page_idx][PageSize]>>;

        page_mem_status := "write_last";

      or \* write_crc
        await page_mem_status = "write_last";

        memory_pages[page_mem_current_page_idx][PageSize] :=
          user_buffer[page_mem_current_buf_offset + PageSize - 1];

        \* Кластер считается валидным после записи последнего байта в последнюю страницу
        set_half_cluster_state(TRUE);

        assert Len(user_buffer) = ClusterSize;
        validate_page_mem_op();
        page_mem_status := "idle";
      end either;
    end while;
end process;

end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "4936f3f8" /\ chksum(tla) = "a2c84c99")
\* Label ResetTick of process reset at line 102 col 5 changed to ResetTick_
VARIABLES pages_per_half_cluster, half_clusters_count, clusters_count, 
          memory_pages, user_buffer, client_init, cluster_idx, cluster_status, 
          cluster_states, current_write_half, current_cluster_state_idx, 
          page_mem_current_buf_offset, page_mem_current_page_idx, 
          page_mem_mess_crc, page_mem_status, client_init_queue, next_status, 
          page_idx, user_buf_offset, crc_1_ok, crc_2_ok, ee_crc_1_ok, 
          ee_crc_2_ok

vars == << pages_per_half_cluster, half_clusters_count, clusters_count, 
           memory_pages, user_buffer, client_init, cluster_idx, 
           cluster_status, cluster_states, current_write_half, 
           current_cluster_state_idx, page_mem_current_buf_offset, 
           page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, 
           client_init_queue, next_status, page_idx, user_buf_offset, 
           crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok >>

ProcSet == {"Reset"} \cup {"Client"} \cup {"Cluster"} \cup {"PageMem"}

Init == (* Global variables *)
        /\ pages_per_half_cluster = (ClusterSize \div PageSize)
        /\ half_clusters_count = get_half_clusters_count(PagesCount, PageSize, ClusterSize)
        /\ clusters_count = (half_clusters_count \div 2)
        /\ memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)]
        /\ user_buffer = SeqOfNElements(INIT_MEM_VALUE, ClusterSize)
        /\ client_init = TRUE
        /\ cluster_idx = 0
        /\ cluster_status = "st_free"
        /\ cluster_states = [state \in 1..half_clusters_count |-> NULL]
        /\ current_write_half = 1
        /\ current_cluster_state_idx = NULL
        /\ page_mem_current_buf_offset = 1
        /\ page_mem_current_page_idx = 1
        /\ page_mem_mess_crc = FALSE
        /\ page_mem_status = "idle"
        (* Process client *)
        /\ client_init_queue = <<>>
        (* Process cluster *)
        /\ next_status = "st_free"
        /\ page_idx = 0
        /\ user_buf_offset = 0
        /\ crc_1_ok = FALSE
        /\ crc_2_ok = FALSE
        /\ ee_crc_1_ok = FALSE
        /\ ee_crc_2_ok = FALSE

reset == /\ \/ /\ cluster_status' = "st_init"
               /\ page_mem_status' = "init"
               /\ client_init' = TRUE
            \/ /\ TRUE
               /\ UNCHANGED <<client_init, cluster_status, page_mem_status>>
         /\ UNCHANGED << pages_per_half_cluster, half_clusters_count, 
                         clusters_count, memory_pages, user_buffer, 
                         cluster_idx, cluster_states, current_write_half, 
                         current_cluster_state_idx, 
                         page_mem_current_buf_offset, 
                         page_mem_current_page_idx, page_mem_mess_crc, 
                         client_init_queue, next_status, page_idx, 
                         user_buf_offset, crc_1_ok, crc_2_ok, ee_crc_1_ok, 
                         ee_crc_2_ok >>

client == /\ IF client_init
                THEN /\ client_init' = FALSE
                     /\ client_init_queue' = [x \in 1..clusters_count |-> (x - 1)]
                     /\ UNCHANGED << user_buffer, cluster_idx, cluster_status >>
                ELSE /\ \/ /\ Len(client_init_queue) /= 0 /\ cluster_status = "st_free"
                           /\ cluster_idx' = Head(client_init_queue)
                           /\ client_init_queue' = Tail(client_init_queue)
                           /\ user_buffer' = SeqOfNElements(INIT_MEM_VALUE, 2 * ClusterSize)
                           /\ cluster_status' = "st_read_begin"
                        \/ /\ Len(client_init_queue) = 0 /\ cluster_status = "st_free"
                           /\ \E idx \in 0..(clusters_count - 1):
                                cluster_idx' = idx
                           /\ user_buffer' = SeqOfNElements(INIT_MEM_VALUE, 2 * ClusterSize)
                           /\ cluster_status' = "st_read_begin"
                           /\ UNCHANGED client_init_queue
                        \/ /\ Len(client_init_queue) = 0 /\ cluster_status = "st_free"
                           /\ \E idx \in 0..(clusters_count - 1):
                                cluster_idx' = idx
                           /\ \E data \in ALLOWED_MEM_VALUES:
                                user_buffer' = SeqOfNElements(data, ClusterSize)
                           /\ cluster_status' = "st_write_begin"
                           /\ UNCHANGED client_init_queue
                     /\ UNCHANGED client_init
          /\ UNCHANGED << pages_per_half_cluster, half_clusters_count, 
                          clusters_count, memory_pages, cluster_states, 
                          current_write_half, current_cluster_state_idx, 
                          page_mem_current_buf_offset, 
                          page_mem_current_page_idx, page_mem_mess_crc, 
                          page_mem_status, next_status, page_idx, 
                          user_buf_offset, crc_1_ok, crc_2_ok, ee_crc_1_ok, 
                          ee_crc_2_ok >>

cluster == /\ \/ /\ cluster_status = "st_init"
                 /\ cluster_status' = "st_free"
                 /\ UNCHANGED <<user_buffer, current_write_half, current_cluster_state_idx, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, next_status, page_idx, user_buf_offset, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ cluster_status = "st_read_begin"
                 /\ page_idx' = get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, 1)
                 /\ user_buf_offset' = 0
                 /\ cluster_status' = "st_read_process"
                 /\ UNCHANGED <<user_buffer, current_write_half, current_cluster_state_idx, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_mess_crc, page_mem_status, next_status, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ cluster_status = "st_read_process" /\ page_mem_status = "idle"
                 /\ IF user_buf_offset < 2 * ClusterSize
                       THEN /\ page_mem_current_buf_offset' = user_buf_offset + 1
                            /\ page_mem_current_page_idx' = page_idx + 1
                            /\ page_mem_status' = "start_read"
                            /\ user_buf_offset' = user_buf_offset + PageSize
                            /\ page_idx' = page_idx + 1
                            /\ UNCHANGED cluster_status
                       ELSE /\ Assert(       user_buffer = full_cluster_content(
                                        memory_pages, cluster_idx, pages_per_half_cluster
                                      ), 
                                      "Failure of assertion at line 202, column 11.")
                            /\ cluster_status' = "st_read_check_crc"
                            /\ UNCHANGED << page_mem_current_buf_offset, 
                                            page_mem_current_page_idx, 
                                            page_mem_status, page_idx, 
                                            user_buf_offset >>
                 /\ UNCHANGED <<user_buffer, current_write_half, current_cluster_state_idx, page_mem_mess_crc, next_status, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ cluster_status = "st_read_check_crc"
                 /\ crc_1_ok' = half_cluster_crc_ok(user_buffer, ClusterSize, 1)
                 /\ crc_2_ok' = half_cluster_crc_ok(user_buffer, ClusterSize, 2)
                 /\ ee_crc_1_ok' = (user_buffer[ClusterSize] = 1)
                 /\ ee_crc_2_ok' = (user_buffer[ClusterSize * 2] = 1)
                 /\ LET first_half_state == cluster_states[get_half_cluster_idx(cluster_idx, 1)] IN
                      LET second_half_state == cluster_states[get_half_cluster_idx(cluster_idx, 2)] IN
                        IF crc_1_ok' /\ ee_crc_1_ok'
                           THEN /\ Assert(first_half_state, 
                                          "Failure of assertion at line 217, column 13.")
                                /\ IF crc_2_ok' /\ ee_crc_2_ok'
                                      THEN /\ Assert(second_half_state, 
                                                     "Failure of assertion at line 220, column 15.")
                                           /\ cluster_status' = "st_free"
                                           /\ UNCHANGED << user_buffer, 
                                                           current_write_half, 
                                                           current_cluster_state_idx, 
                                                           page_mem_mess_crc, 
                                                           next_status, 
                                                           page_idx, 
                                                           user_buf_offset >>
                                      ELSE /\ Assert(/\ second_half_state \in {NULL, FALSE}
                                                     /\ ~half_clusters_equal(user_buffer, ClusterSize), 
                                                     "Failure of assertion at line 224, column 15.")
                                           /\ user_buffer' = SequencePart(user_buffer, 1, ClusterSize)
                                           /\ Assert(2 \in {1, 2}, 
                                                     "Failure of assertion at line 59, column 3 of macro called at line 230, column 15.")
                                           /\ user_buf_offset' = 0
                                           /\ page_idx' = get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, 2)
                                           /\ page_mem_mess_crc' = TRUE
                                           /\ current_cluster_state_idx' = get_half_cluster_idx(cluster_idx, 2)
                                           /\ current_write_half' = 2
                                           /\ next_status' = "st_free"
                                           /\ cluster_status' = "st_write_process"
                           ELSE /\ IF crc_2_ok' /\ ee_crc_2_ok'
                                      THEN /\ Assert(/\ first_half_state /= NULL
                                                     /\ ~first_half_state /\ second_half_state
                                                     /\ ~half_clusters_equal(user_buffer, ClusterSize), 
                                                     "Failure of assertion at line 238, column 15.")
                                           /\ user_buffer' = SequencePart(user_buffer, ClusterSize + 1, ClusterSize)
                                           /\ Assert(1 \in {1, 2}, 
                                                     "Failure of assertion at line 59, column 3 of macro called at line 245, column 15.")
                                           /\ user_buf_offset' = 0
                                           /\ page_idx' = get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, 1)
                                           /\ page_mem_mess_crc' = TRUE
                                           /\ current_cluster_state_idx' = get_half_cluster_idx(cluster_idx, 1)
                                           /\ current_write_half' = 1
                                           /\ next_status' = "st_free"
                                           /\ cluster_status' = "st_write_process"
                                      ELSE /\ Assert(second_half_state = NULL, 
                                                     "Failure of assertion at line 253, column 15.")
                                           /\ user_buffer' = SeqOfNElements(Min(ALLOWED_MEM_VALUES), ClusterSize)
                                           /\ cluster_status' = "st_write_begin"
                                           /\ UNCHANGED << current_write_half, 
                                                           current_cluster_state_idx, 
                                                           page_mem_mess_crc, 
                                                           next_status, 
                                                           page_idx, 
                                                           user_buf_offset >>
                 /\ UNCHANGED <<page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_status>>
              \/ /\ cluster_status = "st_write_begin"
                 /\ Assert(1 \in {1, 2}, 
                           "Failure of assertion at line 59, column 3 of macro called at line 266, column 9.")
                 /\ user_buf_offset' = 0
                 /\ page_idx' = get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, 1)
                 /\ page_mem_mess_crc' = TRUE
                 /\ current_cluster_state_idx' = get_half_cluster_idx(cluster_idx, 1)
                 /\ current_write_half' = 1
                 /\ user_buffer' = [user_buffer EXCEPT ![ClusterSize] = 1]
                 /\ next_status' = "st_write_begin_2_half"
                 /\ cluster_status' = "st_write_process"
                 /\ UNCHANGED <<page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_status, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ cluster_status = "st_write_process" /\ page_mem_status = "idle"
                 /\ IF user_buf_offset + PageSize >= ClusterSize
                       THEN /\ current_cluster_state_idx' = get_half_cluster_idx(cluster_idx, current_write_half)
                       ELSE /\ TRUE
                            /\ UNCHANGED current_cluster_state_idx
                 /\ IF user_buf_offset < ClusterSize
                       THEN /\ page_mem_current_buf_offset' = user_buf_offset + 1
                            /\ page_mem_current_page_idx' = page_idx + 1
                            /\ page_mem_status' = "start_write"
                            /\ user_buf_offset' = user_buf_offset + PageSize
                            /\ page_idx' = page_idx + 1
                            /\ UNCHANGED cluster_status
                       ELSE /\ cluster_status' = next_status
                            /\ Assert(     cluster_status' = "st_free" =>
                                      /\ user_buffer = first_half_cluster_content(memory_pages, cluster_idx, pages_per_half_cluster)
                                      /\ user_buffer = second_half_cluster_content(memory_pages, cluster_idx, pages_per_half_cluster), 
                                      "Failure of assertion at line 53, column 3 of macro called at line 291, column 11.")
                            /\ UNCHANGED << page_mem_current_buf_offset, 
                                            page_mem_current_page_idx, 
                                            page_mem_status, page_idx, 
                                            user_buf_offset >>
                 /\ UNCHANGED <<user_buffer, current_write_half, page_mem_mess_crc, next_status, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
              \/ /\ cluster_status = "st_write_begin_2_half"
                 /\ Assert(2 \in {1, 2}, 
                           "Failure of assertion at line 59, column 3 of macro called at line 298, column 9.")
                 /\ user_buf_offset' = 0
                 /\ page_idx' = get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, 2)
                 /\ page_mem_mess_crc' = TRUE
                 /\ current_cluster_state_idx' = get_half_cluster_idx(cluster_idx, 2)
                 /\ current_write_half' = 2
                 /\ next_status' = "st_free"
                 /\ cluster_status' = "st_write_process"
                 /\ UNCHANGED <<user_buffer, page_mem_current_buf_offset, page_mem_current_page_idx, page_mem_status, crc_1_ok, crc_2_ok, ee_crc_1_ok, ee_crc_2_ok>>
           /\ UNCHANGED << pages_per_half_cluster, half_clusters_count, 
                           clusters_count, memory_pages, client_init, 
                           cluster_idx, cluster_states, client_init_queue >>

page_mem == /\ \/ /\ page_mem_status = "init"
                  /\ page_mem_status' = "idle"
                  /\ UNCHANGED <<memory_pages, user_buffer, cluster_states, current_cluster_state_idx, page_mem_mess_crc>>
               \/ /\ page_mem_status = "idle"
                  /\ UNCHANGED <<memory_pages, user_buffer, cluster_states, current_cluster_state_idx, page_mem_mess_crc, page_mem_status>>
               \/ /\ page_mem_status = "start_read"
                  /\ user_buffer' = [user_buffer EXCEPT ![page_mem_current_buf_offset] = memory_pages[page_mem_current_page_idx][1]]
                  /\ page_mem_status' = "read_tail"
                  /\ UNCHANGED <<memory_pages, cluster_states, current_cluster_state_idx, page_mem_mess_crc>>
               \/ /\ page_mem_status = "read_tail"
                  /\ LET first_user_buf_part_size == page_mem_current_buf_offset + PageSize IN
                       user_buffer' =              SequencePart(user_buffer, 1, page_mem_current_buf_offset) \o
                                      SequencePart(memory_pages[page_mem_current_page_idx], 2, PageSize - 1) \o
                                      SequencePart(
                                        user_buffer, first_user_buf_part_size, Len(user_buffer) - first_user_buf_part_size + 1
                                      )
                  /\ Assert(Len(user_buffer') = ClusterSize * 2, 
                            "Failure of assertion at line 337, column 9.")
                  /\ Assert(       memory_pages[page_mem_current_page_idx] = SequencePart(
                              user_buffer', page_mem_current_buf_offset, PageSize
                            ), 
                            "Failure of assertion at line 78, column 3 of macro called at line 338, column 9.")
                  /\ page_mem_status' = "idle"
                  /\ UNCHANGED <<memory_pages, cluster_states, current_cluster_state_idx, page_mem_mess_crc>>
               \/ /\ page_mem_status = "start_write"
                  /\ LET crc_page == page_mem_current_page_idx + pages_per_half_cluster - 1 IN
                       /\ IF page_mem_mess_crc
                             THEN /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx][1] = user_buffer[page_mem_current_buf_offset],
                                                                          ![crc_page][PageSize] = 0]
                                  /\ IF current_cluster_state_idx /= NULL
                                        THEN /\ IF ~FALSE /\ cluster_states[current_cluster_state_idx] = NULL
                                                   THEN /\ TRUE
                                                        /\ UNCHANGED cluster_states
                                                   ELSE /\ cluster_states' = [cluster_states EXCEPT ![current_cluster_state_idx] = FALSE]
                                             /\ IF pages_per_half_cluster > 1
                                                   THEN /\ current_cluster_state_idx' = NULL
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED current_cluster_state_idx
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << cluster_states, 
                                                             current_cluster_state_idx >>
                             ELSE /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx][1] = user_buffer[page_mem_current_buf_offset]]
                                  /\ UNCHANGED << cluster_states, 
                                                  current_cluster_state_idx >>
                       /\ page_mem_mess_crc' = FALSE
                  /\ page_mem_status' = "write_middle"
                  /\ UNCHANGED user_buffer
               \/ /\ page_mem_status = "write_middle"
                  /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx] =                                          <<user_buffer[page_mem_current_buf_offset]>> \o
                                                                                         SequencePart(user_buffer, page_mem_current_buf_offset + 1, PageSize - 2) \o
                                                                                         <<memory_pages[page_mem_current_page_idx][PageSize]>>]
                  /\ page_mem_status' = "write_last"
                  /\ UNCHANGED <<user_buffer, cluster_states, current_cluster_state_idx, page_mem_mess_crc>>
               \/ /\ page_mem_status = "write_last"
                  /\ memory_pages' = [memory_pages EXCEPT ![page_mem_current_page_idx][PageSize] = user_buffer[page_mem_current_buf_offset + PageSize - 1]]
                  /\ IF current_cluster_state_idx /= NULL
                        THEN /\ IF ~TRUE /\ cluster_states[current_cluster_state_idx] = NULL
                                   THEN /\ TRUE
                                        /\ UNCHANGED cluster_states
                                   ELSE /\ cluster_states' = [cluster_states EXCEPT ![current_cluster_state_idx] = TRUE]
                             /\ IF pages_per_half_cluster > 1
                                   THEN /\ current_cluster_state_idx' = NULL
                                   ELSE /\ TRUE
                                        /\ UNCHANGED current_cluster_state_idx
                        ELSE /\ TRUE
                             /\ UNCHANGED << cluster_states, 
                                             current_cluster_state_idx >>
                  /\ Assert(Len(user_buffer) = ClusterSize, 
                            "Failure of assertion at line 378, column 9.")
                  /\ Assert(       memory_pages'[page_mem_current_page_idx] = SequencePart(
                              user_buffer, page_mem_current_buf_offset, PageSize
                            ), 
                            "Failure of assertion at line 78, column 3 of macro called at line 379, column 9.")
                  /\ page_mem_status' = "idle"
                  /\ UNCHANGED <<user_buffer, page_mem_mess_crc>>
            /\ UNCHANGED << pages_per_half_cluster, half_clusters_count, 
                            clusters_count, client_init, cluster_idx, 
                            cluster_status, current_write_half, 
                            page_mem_current_buf_offset, 
                            page_mem_current_page_idx, client_init_queue, 
                            next_status, page_idx, user_buf_offset, crc_1_ok, 
                            crc_2_ok, ee_crc_1_ok, ee_crc_2_ok >>

Next == reset \/ client \/ cluster \/ page_mem

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(reset)
        /\ WF_vars(client)
        /\ WF_vars(cluster)

\* END TRANSLATION

ClusterStatusInvariant ==
  /\  cluster_status \in {
        "st_init",
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
  "init",
  "idle",
  "start_read",
  "read_tail",
  "start_write",
  "write_middle",
  \* Для последнего значения отдельное состояние, потому что это может
  \* быть crc. Нужно иметь возможность завалиться перед ее записью
  "write_last"
}


PageMemIndexesInvariant ==
  /\ page_mem_current_page_idx \in 1..PagesCount
  /\ page_mem_current_buf_offset \in 1..(2 * ClusterSize + 1)

====

