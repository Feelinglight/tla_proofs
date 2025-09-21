---- MODULE eeprom_safe_map ----
EXTENDS TLC, Integers, utils, SequencesExt, FiniteSets, Sequences

CONSTANTS PagesCount, PageSize, NULL, INIT_MEM_VALUE, ALLOWED_MEM_VALUES,
  MAX_KEYS_COUNT, SECTOR_SIZE_PAGES, DATA_SECTORS_COUNT

ASSUME PagesCount \in Nat \ {0}
ASSUME PageSize \in Nat \ {0}

\* 0 и 1 используются под состояние чексуммы
ASSUME INIT_MEM_VALUE \in Nat \ {0}
ASSUME ALLOWED_MEM_VALUES \subseteq (Nat \ {0, 1})

ASSUME MAX_KEYS_COUNT \in Nat \ {0}
ASSUME SECTOR_SIZE_PAGES \in Nat \ {0}
ASSUME DATA_SECTORS_COUNT \in Nat \ {0}

(*--algorithm mem_cluster
variables
  \* read write
  memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)],

  client_init = TRUE,

  page_mem = [
    status |-> "idle", page_idx |-> 1, buffer |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)
  ];

macro change_key(key, action_status) begin
  map_status := "find_current_key";
  current_key := key;
  action := action_status;
end macro;

macro read_page(page_index, next_status) begin
  page_mem_page_index := current_sector * SECTOR_SIZE_PAGES + page_index;
  page_mem_op := "read";
  map_status := "wait_page_mem";
  next_map_status := next_status;
end macro;

macro write_page(page_index, next_status) begin
  page_mem_page_index := current_sector * SECTOR_SIZE_PAGES + page_index;
  page_mem_op := "write";
  map_status := "wait_page_mem";
  next_map_status := next_status;
end macro;

macro write_key(key_index, key) begin
  cluster_status := "start_write_key";
  cluster_write_key := key;
  cluster_write_key_index := key_index;
end macro;

macro write_value(value_cell, value) begin
  page_buffer := ReplaceAt(page_buffer, value_cell, value);
end macro;

macro add_new_key_tick() begin
  either
    await add_new_key_status = "update_info";

    keys := Append(keys, current_key);
    keys_count := 1;

    if keys_count <= DATA_SECTORS_COUNT then
      page_buffer := SeqOfNElements(INIT_MEM_VALUE, PageSize);
      current_sector_page := 0;
      add_new_key_status := "clear_data_sector";
    else
      add_new_key_status := "write_key";
    end if;
  or
    await add_new_key_status = "clear_data_sector";

    write_page(current_sector_page, "add_new_key");
    if current_sector_page < SECTOR_SIZE_PAGES - 1 then
      current_sector_page := current_sector_page + 1;
      add_new_key_status := "clear_data_sector";
    else
      add_new_key_status := "write_key";
    end if;
  or
    await add_new_key_status = "write_key";

    write_key(keys_count - 1, current_key);
    add_new_key_status := "write_keys_count";
  or
    await add_new_key_status = "write_keys_count";

    if cluster_status = "ready" then
      cluster_write_count := keys_count;
      cluster_status := "start_write_count";
      add_new_key_status := "wait_write_keys_count";
    end if;
  or
    await add_new_key_status = "wait_write_keys_count";
    if cluster_status = "ready" then
      add_new_key_status := "add_new_key_ended";
    end if;
  end either;
end macro;

macro wait_page_mem_tick() begin
  if page_mem.status = "idle" then
    either
      await page_mem_op = "read";

      page_mem := [
        status |-> "start_read",
        page_idx |-> page_mem_page_index,
        buffer |-> page_buffer
      ];

      page_mem_op := "end_op";
    or
      await page_mem_op = "write";

      page_mem := [
        status |-> "start_write",
        page_idx |-> page_mem_page_index,
        buffer |-> page_buffer
      ];

      page_mem_op := "end_op";
    or
      await page_mem_op = "end_op";
      map_status := next_map_status;
    end either;
  end if;
end macro;

fair process reset = "Reset"
begin
  ResetTick:
    while TRUE do
      either
        page_mem.status := "init";
      or
        skip;
      end either;
    end while;
end process;

fair process client = "Client"
begin
  ResetTick:
    while TRUE do
      skip;
    end while;
end process;


process page_mem = "PageMem"
begin
  PageMemTick:
    while TRUE do
      either \* init
        await page_mem.status = "init";

        page_mem.status := "idle";

      or \* idle
        await page_mem.status = "idle";

      \* ---------- Чтение ----------
      or \* start_read
        await page_mem.status = "start_read";

        page_mem.buffer[1] := memory_pages[page_mem.page_idx][1] ||
        page_mem.status := "read_tail";

      or \* read_tail
        await page_mem.status = "read_tail";

        page_mem.buffer := SequencePart(page_mem.buffer, 1, 1) \o
          SequencePart(memory_pages[page_mem.page_idx], 2, PageSize - 1) ||
        page_mem.status := "idle";

        assert
          /\ Len(page_mem.buffer) = PageSize
          /\ memory_pages[page_mem.page_idx] = page_mem.buffer;

      \* ---------- Запись ----------
      or \* start_write
        await page_mem.status = "start_write";

        memory_pages[page_mem.page_idx][1] := page_mem.buffer[1];

        page_mem.status := "write_tail";
      or \* write_tail
        await page_mem.status = "write_tail";

        memory_pages[page_mem.page_idx] := <<page_mem.buffer[1]>> \o
          SequencePart(page_mem.buffer, 2, PageSize - 1);

        assert
          /\ Len(page_mem.buffer) = PageSize
          /\ memory_pages[page_mem.page_idx] = page_mem.buffer;

        page_mem.status := "idle";
      end either;
    end while;
end process;

process cluster = "Cluster"
variables
  cluster_status = "init",
  cluster_write_key = 0,
  cluster_write_key_index = 0,
  cluster_keys = SeqOfNElements(INIT_MEM_VALUE, MAX_KEYS_COUNT),
  cluster_write_count = INIT_MEM_VALUE,
  cluster_keys_count = 0;
begin
  ClusterTick:
    while TRUE do
      either \* init
        await cluster_status = "init";

        cluster_status := "ready";

      or \* ready
        await cluster_status = "ready";

      or \* start_write
        await cluster_status = "start_write_key";
        assert cluster_write_key_index < MAX_KEYS_COUNT;
        cluster_status := "write_tail_key";
      or \* write_tail
        await cluster_status = "write_tail_key";
        cluster_keys := ReplaceAt(cluster_keys, cluster_write_key_index + 1, cluster_write_key);
        cluster_status := "ready";

      or \* start_write_count
        await cluster_status = "start_write_count";
        assert cluster_write_count = cluster_keys_count + 1;
        cluster_status := "write_tail_count";
      or \* write_tail
        await cluster_status = "write_tail_count";
        cluster_keys_count := cluster_write_count;
        cluster_status := "ready";
      end either;
    end while;
end process;

process map = "Map"
variables
  keys = <<>>,
  keys_count = 0,

  page_buffer = SeqOfNElements(INIT_MEM_VALUE, PageSize),

  map_status = "free",
  next_map_status = "free",

  action = "read_value",
  add_new_key_status = "update_info",
  replace_key_status = "read_value_page",

  page_mem_op = "read",
  current_key = 0,
  new_value = CHOOSE x \in ALLOWED_MEM_VALUES: TRUE,
  value_buffer = NULL,

  current_key_index = 0,
  current_sector = 0,
  current_sector_page = 0,
  current_value_cell = 0,

  page_mem_page_index = 0;

  first_read = TRUE,
  actual_value = 0;

begin
  MapTick:
    either
      await map_status = "init";
    or
      await map_status = "free";
    or
      await map_status = "find_current_key";

      with search_res = IndexAndResult(keys, current_key) do
        current_key_index := search_res.index;
        current_sector := current_key_index % DATA_SECTORS_COUNT;
        current_value_cell := current_key_index \div DATA_SECTORS_COUNT;

        if search_res.found = FALSE then
          map_status := "add_new_key";
          add_new_key_status := "update_info";
        else
          current_sector_page := 0;

          if action = "replace_key" then
            replace_key_status := "replace_value";
            read_page(0, "reset_sector_values");
          else
            actual_value := 0;
            read_page(0, "find_actual_value");
          end if;
        end if;
      end with;
    or
      await map_status = "add_new_key";
      add_new_key_tick();
    or
      await map_status = "add_new_key_ended";

      current_sector_page := 0;
      actual_value := 0;
      read_page(0, "write_new_value");

    or
      await map_status = "reset_sector_values";
      \* дописать replace_key
      \* reset_values_for_key_replace_tick();
    or
      await map_status = "find_actual_value";
      assert current_sector_page < SECTOR_SIZE_PAGES;

      with
        current_value_less = page_buffer[current_value_cell] < actual_value,
        current_value_last = current_sector_page = SECTOR_SIZE_PAGES - 1,
        current_value = page_buffer[current_value_cell]
      do
        if current_value_less \/ current_value_last then
          assert action /= "replace_key";

          if current_value_less then
            assert current_sector_page /= 0;
          elsif current_value_last then
            actual_value := current_value;
          end if;

          if action = "read_value" then
            value_buffer := actual_value;
            map_status := "free";
          else
            if current_value_last then
              \* дописать: кажется здесь можно просто присвоить 0
              current_sector_page := (current_sector_page + 1) % SECTOR_SIZE_PAGES;
            end if;
            read_page(current_sector_page, "write_new_value");
          end if;
        else
          actual_value := current_value;
          current_sector_page := current_sector_page + 1;
          read_page(current_sector_page, "find_actual_value");
        end if;
      end with

    or
      await map_status = "write_new_value";
      actual_value := actual_value + new_value;
      write_value(current_value_cell, actual_value);
      write_page(current_sector_page, "free");
    or
      await map_status = "wait_page_mem";
      wait_page_mem_tick();
    end either;
end process;


process map_client = "MapClient"
variables
  map_command = "no_command";
begin
  MapClientTick:
    either \* clear
      await map_status = "free";
      print(DATA_SECTORS_COUNT);
    or \* increment_value
      await map_status = "free";

      with key \in ALLOWED_MEM_VALUES, increment \in ALLOWED_MEM_VALUES do
        if ~Contains(keys, increment) /\ keys_count = MAX_KEYS_COUNT then
          \* assert
          skip;
        else
          new_value := increment;
          if current_key /= key \/ keys_count = 0 then
            change_key(key, "write_value");
          else
            current_sector_page := (current_sector_page + 1) % SECTOR_SIZE_PAGES;
            read_page(current_sector_page, "write_new_value");
          end if;
        end if;
      end with;
    or \* get_value
      await map_status = "free";
    or \* replace_key
      await map_status = "free";
    or \* update_value
      await map_status = "free";
    end either;
end process;

end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "a764eab8" /\ chksum(tla) = "7ddd14c8")
\* Label ResetTick of process reset at line 136 col 5 changed to ResetTick_
\* Process page_mem at line 154 col 1 changed to page_mem_
VARIABLES pc, memory_pages, client_init, page_mem, cluster_status, 
          cluster_write_key, cluster_write_key_index, cluster_keys, 
          cluster_write_count, cluster_keys_count, keys, keys_count, 
          page_buffer, map_status, next_map_status, action, 
          add_new_key_status, replace_key_status, page_mem_op, current_key, 
          new_value, value_buffer, current_key_index, current_sector, 
          current_sector_page, current_value_cell, page_mem_page_index, 
          first_read, actual_value, map_command

vars == << pc, memory_pages, client_init, page_mem, cluster_status, 
           cluster_write_key, cluster_write_key_index, cluster_keys, 
           cluster_write_count, cluster_keys_count, keys, keys_count, 
           page_buffer, map_status, next_map_status, action, 
           add_new_key_status, replace_key_status, page_mem_op, current_key, 
           new_value, value_buffer, current_key_index, current_sector, 
           current_sector_page, current_value_cell, page_mem_page_index, 
           first_read, actual_value, map_command >>

ProcSet == {"Reset"} \cup {"Client"} \cup {"PageMem"} \cup {"Cluster"} \cup {"Map"} \cup {"MapClient"}

Init == (* Global variables *)
        /\ memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)]
        /\ client_init = TRUE
        /\ page_mem =            [
                        status |-> "idle", page_idx |-> 1, buffer |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)
                      ]
        (* Process cluster *)
        /\ cluster_status = "init"
        /\ cluster_write_key = 0
        /\ cluster_write_key_index = 0
        /\ cluster_keys = SeqOfNElements(INIT_MEM_VALUE, MAX_KEYS_COUNT)
        /\ cluster_write_count = INIT_MEM_VALUE
        /\ cluster_keys_count = 0
        (* Process map *)
        /\ keys = <<>>
        /\ keys_count = 0
        /\ page_buffer = SeqOfNElements(INIT_MEM_VALUE, PageSize)
        /\ map_status = "free"
        /\ next_map_status = "free"
        /\ action = "read_value"
        /\ add_new_key_status = "update_info"
        /\ replace_key_status = "read_value_page"
        /\ page_mem_op = "read"
        /\ current_key = 0
        /\ new_value = CHOOSE x \in ALLOWED_MEM_VALUES: TRUE
        /\ value_buffer = NULL
        /\ current_key_index = 0
        /\ current_sector = 0
        /\ current_sector_page = 0
        /\ current_value_cell = 0
        /\ page_mem_page_index = 0
        /\ first_read = TRUE
        /\ actual_value = 0
        (* Process map_client *)
        /\ map_command = "no_command"
        /\ pc = [self \in ProcSet |-> CASE self = "Reset" -> "ResetTick_"
                                        [] self = "Client" -> "ResetTick"
                                        [] self = "PageMem" -> "PageMemTick"
                                        [] self = "Cluster" -> "ClusterTick"
                                        [] self = "Map" -> "MapTick"
                                        [] self = "MapClient" -> "MapClientTick"]

ResetTick_ == /\ pc["Reset"] = "ResetTick_"
              /\ \/ /\ page_mem' = [page_mem EXCEPT !.status = "init"]
                 \/ /\ TRUE
                    /\ UNCHANGED page_mem
              /\ pc' = [pc EXCEPT !["Reset"] = "ResetTick_"]
              /\ UNCHANGED << memory_pages, client_init, cluster_status, 
                              cluster_write_key, cluster_write_key_index, 
                              cluster_keys, cluster_write_count, 
                              cluster_keys_count, keys, keys_count, 
                              page_buffer, map_status, next_map_status, action, 
                              add_new_key_status, replace_key_status, 
                              page_mem_op, current_key, new_value, 
                              value_buffer, current_key_index, current_sector, 
                              current_sector_page, current_value_cell, 
                              page_mem_page_index, first_read, actual_value, 
                              map_command >>

reset == ResetTick_

ResetTick == /\ pc["Client"] = "ResetTick"
             /\ TRUE
             /\ pc' = [pc EXCEPT !["Client"] = "ResetTick"]
             /\ UNCHANGED << memory_pages, client_init, page_mem, 
                             cluster_status, cluster_write_key, 
                             cluster_write_key_index, cluster_keys, 
                             cluster_write_count, cluster_keys_count, keys, 
                             keys_count, page_buffer, map_status, 
                             next_map_status, action, add_new_key_status, 
                             replace_key_status, page_mem_op, current_key, 
                             new_value, value_buffer, current_key_index, 
                             current_sector, current_sector_page, 
                             current_value_cell, page_mem_page_index, 
                             first_read, actual_value, map_command >>

client == ResetTick

PageMemTick == /\ pc["PageMem"] = "PageMemTick"
               /\ \/ /\ page_mem.status = "init"
                     /\ page_mem' = [page_mem EXCEPT !.status = "idle"]
                     /\ UNCHANGED memory_pages
                  \/ /\ page_mem.status = "idle"
                     /\ UNCHANGED <<memory_pages, page_mem>>
                  \/ /\ page_mem.status = "start_read"
                     /\ page_mem' = [page_mem EXCEPT !.buffer[1] = memory_pages[page_mem.page_idx][1],
                                                     !.status = "read_tail"]
                     /\ UNCHANGED memory_pages
                  \/ /\ page_mem.status = "read_tail"
                     /\ page_mem' = [page_mem EXCEPT !.buffer =                  SequencePart(page_mem.buffer, 1, 1) \o
                                                                SequencePart(memory_pages[page_mem.page_idx], 2, PageSize - 1),
                                                     !.status = "idle"]
                     /\ Assert(/\ Len(page_mem'.buffer) = PageSize
                               /\ memory_pages[page_mem'.page_idx] = page_mem'.buffer, 
                               "Failure of assertion at line 180, column 9.")
                     /\ UNCHANGED memory_pages
                  \/ /\ page_mem.status = "start_write"
                     /\ memory_pages' = [memory_pages EXCEPT ![page_mem.page_idx][1] = page_mem.buffer[1]]
                     /\ page_mem' = [page_mem EXCEPT !.status = "write_tail"]
                  \/ /\ page_mem.status = "write_tail"
                     /\ memory_pages' = [memory_pages EXCEPT ![page_mem.page_idx] =                                  <<page_mem.buffer[1]>> \o
                                                                                    SequencePart(page_mem.buffer, 2, PageSize - 1)]
                     /\ Assert(/\ Len(page_mem.buffer) = PageSize
                               /\ memory_pages'[page_mem.page_idx] = page_mem.buffer, 
                               "Failure of assertion at line 197, column 9.")
                     /\ page_mem' = [page_mem EXCEPT !.status = "idle"]
               /\ pc' = [pc EXCEPT !["PageMem"] = "PageMemTick"]
               /\ UNCHANGED << client_init, cluster_status, cluster_write_key, 
                               cluster_write_key_index, cluster_keys, 
                               cluster_write_count, cluster_keys_count, keys, 
                               keys_count, page_buffer, map_status, 
                               next_map_status, action, add_new_key_status, 
                               replace_key_status, page_mem_op, current_key, 
                               new_value, value_buffer, current_key_index, 
                               current_sector, current_sector_page, 
                               current_value_cell, page_mem_page_index, 
                               first_read, actual_value, map_command >>

page_mem_ == PageMemTick

ClusterTick == /\ pc["Cluster"] = "ClusterTick"
               /\ \/ /\ cluster_status = "init"
                     /\ cluster_status' = "ready"
                     /\ UNCHANGED <<cluster_keys, cluster_keys_count>>
                  \/ /\ cluster_status = "ready"
                     /\ UNCHANGED <<cluster_status, cluster_keys, cluster_keys_count>>
                  \/ /\ cluster_status = "start_write_key"
                     /\ Assert(cluster_write_key_index < MAX_KEYS_COUNT, 
                               "Failure of assertion at line 227, column 9.")
                     /\ cluster_status' = "write_tail_key"
                     /\ UNCHANGED <<cluster_keys, cluster_keys_count>>
                  \/ /\ cluster_status = "write_tail_key"
                     /\ cluster_keys' = ReplaceAt(cluster_keys, cluster_write_key_index + 1, cluster_write_key)
                     /\ cluster_status' = "ready"
                     /\ UNCHANGED cluster_keys_count
                  \/ /\ cluster_status = "start_write_count"
                     /\ Assert(cluster_write_count = cluster_keys_count + 1, 
                               "Failure of assertion at line 236, column 9.")
                     /\ cluster_status' = "write_tail_count"
                     /\ UNCHANGED <<cluster_keys, cluster_keys_count>>
                  \/ /\ cluster_status = "write_tail_count"
                     /\ cluster_keys_count' = cluster_write_count
                     /\ cluster_status' = "ready"
                     /\ UNCHANGED cluster_keys
               /\ pc' = [pc EXCEPT !["Cluster"] = "ClusterTick"]
               /\ UNCHANGED << memory_pages, client_init, page_mem, 
                               cluster_write_key, cluster_write_key_index, 
                               cluster_write_count, keys, keys_count, 
                               page_buffer, map_status, next_map_status, 
                               action, add_new_key_status, replace_key_status, 
                               page_mem_op, current_key, new_value, 
                               value_buffer, current_key_index, current_sector, 
                               current_sector_page, current_value_cell, 
                               page_mem_page_index, first_read, actual_value, 
                               map_command >>

cluster == ClusterTick

MapTick == /\ pc["Map"] = "MapTick"
           /\ \/ /\ map_status = "init"
                 /\ UNCHANGED <<page_mem, cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, page_buffer, map_status, next_map_status, add_new_key_status, replace_key_status, page_mem_op, value_buffer, current_key_index, current_sector, current_sector_page, current_value_cell, page_mem_page_index, actual_value>>
              \/ /\ map_status = "free"
                 /\ UNCHANGED <<page_mem, cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, page_buffer, map_status, next_map_status, add_new_key_status, replace_key_status, page_mem_op, value_buffer, current_key_index, current_sector, current_sector_page, current_value_cell, page_mem_page_index, actual_value>>
              \/ /\ map_status = "find_current_key"
                 /\ LET search_res == IndexAndResult(keys, current_key) IN
                      /\ current_key_index' = search_res.index
                      /\ current_sector' = current_key_index' % DATA_SECTORS_COUNT
                      /\ current_value_cell' = (current_key_index' \div DATA_SECTORS_COUNT)
                      /\ IF search_res.found = FALSE
                            THEN /\ map_status' = "add_new_key"
                                 /\ add_new_key_status' = "update_info"
                                 /\ UNCHANGED << next_map_status, 
                                                 replace_key_status, 
                                                 page_mem_op, 
                                                 current_sector_page, 
                                                 page_mem_page_index, 
                                                 actual_value >>
                            ELSE /\ current_sector_page' = 0
                                 /\ IF action = "replace_key"
                                       THEN /\ replace_key_status' = "replace_value"
                                            /\ page_mem_page_index' = current_sector' * SECTOR_SIZE_PAGES + 0
                                            /\ page_mem_op' = "read"
                                            /\ map_status' = "wait_page_mem"
                                            /\ next_map_status' = "reset_sector_values"
                                            /\ UNCHANGED actual_value
                                       ELSE /\ actual_value' = 0
                                            /\ page_mem_page_index' = current_sector' * SECTOR_SIZE_PAGES + 0
                                            /\ page_mem_op' = "read"
                                            /\ map_status' = "wait_page_mem"
                                            /\ next_map_status' = "find_actual_value"
                                            /\ UNCHANGED replace_key_status
                                 /\ UNCHANGED add_new_key_status
                 /\ UNCHANGED <<page_mem, cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, page_buffer, value_buffer>>
              \/ /\ map_status = "add_new_key"
                 /\ \/ /\ add_new_key_status = "update_info"
                       /\ keys' = Append(keys, current_key)
                       /\ keys_count' = 1
                       /\ IF keys_count' <= DATA_SECTORS_COUNT
                             THEN /\ page_buffer' = SeqOfNElements(INIT_MEM_VALUE, PageSize)
                                  /\ current_sector_page' = 0
                                  /\ add_new_key_status' = "clear_data_sector"
                             ELSE /\ add_new_key_status' = "write_key"
                                  /\ UNCHANGED << page_buffer, 
                                                  current_sector_page >>
                       /\ UNCHANGED <<cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, map_status, next_map_status, page_mem_op, page_mem_page_index>>
                    \/ /\ add_new_key_status = "clear_data_sector"
                       /\ page_mem_page_index' = current_sector * SECTOR_SIZE_PAGES + current_sector_page
                       /\ page_mem_op' = "write"
                       /\ map_status' = "wait_page_mem"
                       /\ next_map_status' = "add_new_key"
                       /\ IF current_sector_page < SECTOR_SIZE_PAGES - 1
                             THEN /\ current_sector_page' = current_sector_page + 1
                                  /\ add_new_key_status' = "clear_data_sector"
                             ELSE /\ add_new_key_status' = "write_key"
                                  /\ UNCHANGED current_sector_page
                       /\ UNCHANGED <<cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, page_buffer>>
                    \/ /\ add_new_key_status = "write_key"
                       /\ cluster_status' = "start_write_key"
                       /\ cluster_write_key' = current_key
                       /\ cluster_write_key_index' = keys_count - 1
                       /\ add_new_key_status' = "write_keys_count"
                       /\ UNCHANGED <<cluster_write_count, keys, keys_count, page_buffer, map_status, next_map_status, page_mem_op, current_sector_page, page_mem_page_index>>
                    \/ /\ add_new_key_status = "write_keys_count"
                       /\ IF cluster_status = "ready"
                             THEN /\ cluster_write_count' = keys_count
                                  /\ cluster_status' = "start_write_count"
                                  /\ add_new_key_status' = "wait_write_keys_count"
                             ELSE /\ TRUE
                                  /\ UNCHANGED << cluster_status, 
                                                  cluster_write_count, 
                                                  add_new_key_status >>
                       /\ UNCHANGED <<cluster_write_key, cluster_write_key_index, keys, keys_count, page_buffer, map_status, next_map_status, page_mem_op, current_sector_page, page_mem_page_index>>
                    \/ /\ add_new_key_status = "wait_write_keys_count"
                       /\ IF cluster_status = "ready"
                             THEN /\ add_new_key_status' = "add_new_key_ended"
                             ELSE /\ TRUE
                                  /\ UNCHANGED add_new_key_status
                       /\ UNCHANGED <<cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, page_buffer, map_status, next_map_status, page_mem_op, current_sector_page, page_mem_page_index>>
                 /\ UNCHANGED <<page_mem, replace_key_status, value_buffer, current_key_index, current_sector, current_value_cell, actual_value>>
              \/ /\ map_status = "add_new_key_ended"
                 /\ current_sector_page' = 0
                 /\ actual_value' = 0
                 /\ page_mem_page_index' = current_sector * SECTOR_SIZE_PAGES + 0
                 /\ page_mem_op' = "read"
                 /\ map_status' = "wait_page_mem"
                 /\ next_map_status' = "write_new_value"
                 /\ UNCHANGED <<page_mem, cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, page_buffer, add_new_key_status, replace_key_status, value_buffer, current_key_index, current_sector, current_value_cell>>
              \/ /\ map_status = "reset_sector_values"
                 /\ UNCHANGED <<page_mem, cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, page_buffer, map_status, next_map_status, add_new_key_status, replace_key_status, page_mem_op, value_buffer, current_key_index, current_sector, current_sector_page, current_value_cell, page_mem_page_index, actual_value>>
              \/ /\ map_status = "find_actual_value"
                 /\ Assert(current_sector_page < SECTOR_SIZE_PAGES, 
                           "Failure of assertion at line 320, column 7.")
                 /\ LET current_value_less == page_buffer[current_value_cell] < actual_value IN
                      LET current_value_last == current_sector_page = SECTOR_SIZE_PAGES - 1 IN
                        LET current_value == page_buffer[current_value_cell] IN
                          IF current_value_less \/ current_value_last
                             THEN /\ Assert(action /= "replace_key", 
                                            "Failure of assertion at line 328, column 11.")
                                  /\ IF current_value_less
                                        THEN /\ Assert(current_sector_page /= 0, 
                                                       "Failure of assertion at line 331, column 13.")
                                             /\ UNCHANGED actual_value
                                        ELSE /\ IF current_value_last
                                                   THEN /\ actual_value' = current_value
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED actual_value
                                  /\ IF action = "read_value"
                                        THEN /\ value_buffer' = actual_value'
                                             /\ map_status' = "free"
                                             /\ UNCHANGED << next_map_status, 
                                                             page_mem_op, 
                                                             current_sector_page, 
                                                             page_mem_page_index >>
                                        ELSE /\ IF current_value_last
                                                   THEN /\ current_sector_page' = (current_sector_page + 1) % SECTOR_SIZE_PAGES
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED current_sector_page
                                             /\ page_mem_page_index' = current_sector * SECTOR_SIZE_PAGES + current_sector_page'
                                             /\ page_mem_op' = "read"
                                             /\ map_status' = "wait_page_mem"
                                             /\ next_map_status' = "write_new_value"
                                             /\ UNCHANGED value_buffer
                             ELSE /\ actual_value' = current_value
                                  /\ current_sector_page' = current_sector_page + 1
                                  /\ page_mem_page_index' = current_sector * SECTOR_SIZE_PAGES + current_sector_page'
                                  /\ page_mem_op' = "read"
                                  /\ map_status' = "wait_page_mem"
                                  /\ next_map_status' = "find_actual_value"
                                  /\ UNCHANGED value_buffer
                 /\ UNCHANGED <<page_mem, cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, page_buffer, add_new_key_status, replace_key_status, current_key_index, current_sector, current_value_cell>>
              \/ /\ map_status = "write_new_value"
                 /\ actual_value' = actual_value + new_value
                 /\ page_buffer' = ReplaceAt(page_buffer, current_value_cell, actual_value')
                 /\ page_mem_page_index' = current_sector * SECTOR_SIZE_PAGES + current_sector_page
                 /\ page_mem_op' = "write"
                 /\ map_status' = "wait_page_mem"
                 /\ next_map_status' = "free"
                 /\ UNCHANGED <<page_mem, cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, add_new_key_status, replace_key_status, value_buffer, current_key_index, current_sector, current_sector_page, current_value_cell>>
              \/ /\ map_status = "wait_page_mem"
                 /\ IF page_mem.status = "idle"
                       THEN /\ \/ /\ page_mem_op = "read"
                                  /\ page_mem' =             [
                                                   status |-> "start_read",
                                                   page_idx |-> page_mem_page_index,
                                                   buffer |-> page_buffer
                                                 ]
                                  /\ page_mem_op' = "end_op"
                                  /\ UNCHANGED map_status
                               \/ /\ page_mem_op = "write"
                                  /\ page_mem' =             [
                                                   status |-> "start_write",
                                                   page_idx |-> page_mem_page_index,
                                                   buffer |-> page_buffer
                                                 ]
                                  /\ page_mem_op' = "end_op"
                                  /\ UNCHANGED map_status
                               \/ /\ page_mem_op = "end_op"
                                  /\ map_status' = next_map_status
                                  /\ UNCHANGED <<page_mem, page_mem_op>>
                       ELSE /\ TRUE
                            /\ UNCHANGED << page_mem, map_status, page_mem_op >>
                 /\ UNCHANGED <<cluster_status, cluster_write_key, cluster_write_key_index, cluster_write_count, keys, keys_count, page_buffer, next_map_status, add_new_key_status, replace_key_status, value_buffer, current_key_index, current_sector, current_sector_page, current_value_cell, page_mem_page_index, actual_value>>
           /\ pc' = [pc EXCEPT !["Map"] = "Done"]
           /\ UNCHANGED << memory_pages, client_init, cluster_keys, 
                           cluster_keys_count, action, current_key, new_value, 
                           first_read, map_command >>

map == MapTick

MapClientTick == /\ pc["MapClient"] = "MapClientTick"
                 /\ \/ /\ map_status = "free"
                       /\ PrintT((DATA_SECTORS_COUNT))
                       /\ UNCHANGED <<map_status, next_map_status, action, page_mem_op, current_key, new_value, current_sector_page, page_mem_page_index>>
                    \/ /\ map_status = "free"
                       /\ \E key \in ALLOWED_MEM_VALUES:
                            \E increment \in ALLOWED_MEM_VALUES:
                              IF ~Contains(keys, increment) /\ keys_count = MAX_KEYS_COUNT
                                 THEN /\ TRUE
                                      /\ UNCHANGED << map_status, 
                                                      next_map_status, action, 
                                                      page_mem_op, current_key, 
                                                      new_value, 
                                                      current_sector_page, 
                                                      page_mem_page_index >>
                                 ELSE /\ new_value' = increment
                                      /\ IF current_key /= key \/ keys_count = 0
                                            THEN /\ map_status' = "find_current_key"
                                                 /\ current_key' = key
                                                 /\ action' = "write_value"
                                                 /\ UNCHANGED << next_map_status, 
                                                                 page_mem_op, 
                                                                 current_sector_page, 
                                                                 page_mem_page_index >>
                                            ELSE /\ current_sector_page' = (current_sector_page + 1) % SECTOR_SIZE_PAGES
                                                 /\ page_mem_page_index' = current_sector * SECTOR_SIZE_PAGES + current_sector_page'
                                                 /\ page_mem_op' = "read"
                                                 /\ map_status' = "wait_page_mem"
                                                 /\ next_map_status' = "write_new_value"
                                                 /\ UNCHANGED << action, 
                                                                 current_key >>
                    \/ /\ map_status = "free"
                       /\ UNCHANGED <<map_status, next_map_status, action, page_mem_op, current_key, new_value, current_sector_page, page_mem_page_index>>
                    \/ /\ map_status = "free"
                       /\ UNCHANGED <<map_status, next_map_status, action, page_mem_op, current_key, new_value, current_sector_page, page_mem_page_index>>
                    \/ /\ map_status = "free"
                       /\ UNCHANGED <<map_status, next_map_status, action, page_mem_op, current_key, new_value, current_sector_page, page_mem_page_index>>
                 /\ pc' = [pc EXCEPT !["MapClient"] = "Done"]
                 /\ UNCHANGED << memory_pages, client_init, page_mem, 
                                 cluster_status, cluster_write_key, 
                                 cluster_write_key_index, cluster_keys, 
                                 cluster_write_count, cluster_keys_count, keys, 
                                 keys_count, page_buffer, add_new_key_status, 
                                 replace_key_status, value_buffer, 
                                 current_key_index, current_sector, 
                                 current_value_cell, first_read, actual_value, 
                                 map_command >>

map_client == MapClientTick

Next == reset \/ client \/ page_mem_ \/ cluster \/ map \/ map_client

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(reset)
        /\ WF_vars(client)

\* END TRANSLATION

MapStatusInvariant == map_status \in {
  "init",
  "free",
  "find_current_key",
  "add_new_key",
  "add_new_key_ended",
  "find_actual_value",
  "reset_sector_values",
  "write_new_value",
  "wait_page_mem"
}

ActionInvariant == action \in {
  "read_value",
  "write_value",
  "replace_key"
}

ReplaceKeyStatusInvariant == replace_key_status \in {
  "read_value_page",
  "replace_value",
  "wait_replace_key"
}

PageOpInvariant == page_mem_op \in {
  "read",
  "write",
  "end_op"
}

AddNewKeyStatusInvariant == add_new_key_status \in {
  "update_info",
  "clear_data_sector",
  "write_key",
  "write_keys_count",
  "wait_write_keys_count"
}

ClusterStatusInvariant == cluster_status \in {
  "init",
  "ready",
  "write_start",
  "write_tail",
  "start_write_count",
  "write_tail_count"
}

PageMemStatusInvariant == page_mem.status \in {
  "init",
  "idle",
  "start_read",
  "read_tail",
  "start_write",
  "write_tail"
}

PageMemIndexesInvariant ==
  /\ page_mem.page_idx \in 1..PagesCount

MapCommandInvariant == map_command \in {
  "no_command",
  "clear",
  "increment_value",
  "get_value",
  "replace_key",
  "update_value"
}

====

