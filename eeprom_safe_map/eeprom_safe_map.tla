---- MODULE eeprom_safe_map ----
EXTENDS TLC, Integers, utils, SequencesExt, FiniteSets

CONSTANTS PagesCount, PageSize, NULL, INIT_MEM_VALUE, ALLOWED_MEM_VALUES,
  MAX_KEYS_COUNT, SECTOR_SIZE_PAGES, CLUSTER_SIZE_PAGES, DATA_SECTORS_COUNT

ASSUME PagesCount \in Nat \ {0}
ASSUME PageSize \in Nat \ {0}

\* 0 и 1 используются под состояние чексуммы
ASSUME INIT_MEM_VALUE \in Nat \ {0}
ASSUME ALLOWED_MEM_VALUES \subseteq (Nat \ {0, 1})

ASSUME MAX_KEYS_COUNT \in Nat \ {0}
ASSUME SECTOR_SIZE_PAGES \in Nat \ {0}
ASSUME CLUSTER_SIZE_PAGES \in Nat \ {0}
ASSUME DATA_SECTORS_COUNT \in Nat \ {0}

(*--algorithm mem_cluster
variables
  \* read write
  memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)],
  user_buffer = SeqOfNElements(INIT_MEM_VALUE, PageSize),

  client_init = TRUE,

  page_mem = [status |-> "idle", page_idx |-> 1];

macro change_key(key, action_status) begin
  map_status := "find_current_key";
  current_key := key;
  action := action_status;
end macro;

macro read_page(page_index, next_status) begin
  page_mem := [status |-> "read", page_idx |-> current_sector * SECTOR_SIZE_PAGES + page_index];
  map_status := "wait_page_mem";
  next_map_status := next_status;
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
      either
        await page_mem.status = "idle";

        user_buffer := SeqOfNElements(INIT_MEM_VALUE, PageSize);

        with idx \in 1..PagesCount do
          page_mem := [status |-> "start_read", page_idx |-> idx];
        end with;
      or
        await page_mem.status = "idle";

        with data \in [ALLOWED_MEM_VALUES -> ALLOWED_MEM_VALUES] do
          user_buffer := SeqOfNElements(data, PageSize);
        end with;

        with idx \in 1..PagesCount do
          page_mem := [status |-> "start_write", page_idx |-> idx];
        end with;

      end either;
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

        user_buffer[1] := memory_pages[page_mem.page_idx][1];

        page_mem.status := "read_tail";

      or \* read_tail
        await page_mem.status = "read_tail";

        user_buffer := SequencePart(user_buffer, 1, 1) \o
          SequencePart(memory_pages[page_mem.page_idx], 2, PageSize - 1);

        assert
          /\ Len(user_buffer) = PageSize
          /\ memory_pages[page_mem.page_idx] = user_buffer;

        page_mem.status := "idle";

      \* ---------- Запись ----------
      or \* start_write
        await page_mem.status = "start_write";

        memory_pages[page_mem.page_idx][1] := user_buffer[1];

        page_mem.status := "write_tail";
      or \* write_tail
        await page_mem.status = "write_tail";

        memory_pages[page_mem.page_idx] := <<user_buffer[1]>> \o
          SequencePart(user_buffer, 2, PageSize - 1);

        assert
          /\ Len(user_buffer) = PageSize
          /\ memory_pages[page_mem.page_idx] = user_buffer;

        page_mem.status := "idle";
      end either;
    end while;
end process;

process map = "Map"
variables
  keys = <<>>,
  keys_count = 0,

  map_status = "free",
  next_map_status = "free",

  action = "read_value",

  current_key = 0,
  new_value = CHOOSE x \in ALLOWED_MEM_VALUES: TRUE,

  current_key_index = 0,
  current_sector = 0,
  current_sector_page = 0,
  current_value_cell = 0,

begin
  MapTick:
    either
      await map_status = "init";
    or
      await map_status = "free";
    or
      await map_status = "find_current_key";
      assert Contains(keys, current_key);

      current_key_index := IndexOf(keys, current_key);

    end either;
end process;


process map_client = "MapClient"
variables
  map_command = "no_command";
begin
  MapClientTick:
    either \* clear
      await map_status = "free";
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


\* BEGIN TRANSLATION (chksum(pcal) = "40ab7f6d" /\ chksum(tla) = "439fec4c")
\* Label ResetTick of process reset at line 44 col 5 changed to ResetTick_
\* Process page_mem at line 81 col 1 changed to page_mem_
VARIABLES pc, memory_pages, user_buffer, client_init, page_mem, keys, 
          keys_count, map_status, next_map_status, action, current_key, 
          new_value, current_key_index, current_sector, current_sector_page, 
          current_value_cell, map_command

vars == << pc, memory_pages, user_buffer, client_init, page_mem, keys, 
           keys_count, map_status, next_map_status, action, current_key, 
           new_value, current_key_index, current_sector, current_sector_page, 
           current_value_cell, map_command >>

ProcSet == {"Reset"} \cup {"Client"} \cup {"PageMem"} \cup {"Map"} \cup {"MapClient"}

Init == (* Global variables *)
        /\ memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)]
        /\ user_buffer = SeqOfNElements(INIT_MEM_VALUE, PageSize)
        /\ client_init = TRUE
        /\ page_mem = [status |-> "idle", page_idx |-> 1]
        (* Process map *)
        /\ keys = <<>>
        /\ keys_count = 0
        /\ map_status = "free"
        /\ next_map_status = "free"
        /\ action = "read_value"
        /\ current_key = 0
        /\ new_value = CHOOSE x \in ALLOWED_MEM_VALUES: TRUE
        /\ current_key_index = 0
        /\ current_sector = 0
        /\ current_sector_page = 0
        /\ current_value_cell = 0
        (* Process map_client *)
        /\ map_command = "no_command"
        /\ pc = [self \in ProcSet |-> CASE self = "Reset" -> "ResetTick_"
                                        [] self = "Client" -> "ResetTick"
                                        [] self = "PageMem" -> "PageMemTick"
                                        [] self = "Map" -> "MapTick"
                                        [] self = "MapClient" -> "MapClientTick"]

ResetTick_ == /\ pc["Reset"] = "ResetTick_"
              /\ \/ /\ page_mem' = [page_mem EXCEPT !.status = "init"]
                 \/ /\ TRUE
                    /\ UNCHANGED page_mem
              /\ pc' = [pc EXCEPT !["Reset"] = "ResetTick_"]
              /\ UNCHANGED << memory_pages, user_buffer, client_init, keys, 
                              keys_count, map_status, next_map_status, action, 
                              current_key, new_value, current_key_index, 
                              current_sector, current_sector_page, 
                              current_value_cell, map_command >>

reset == ResetTick_

ResetTick == /\ pc["Client"] = "ResetTick"
             /\ \/ /\ page_mem.status = "idle"
                   /\ user_buffer' = SeqOfNElements(INIT_MEM_VALUE, PageSize)
                   /\ \E idx \in 1..PagesCount:
                        page_mem' = [status |-> "start_read", page_idx |-> idx]
                \/ /\ page_mem.status = "idle"
                   /\ \E data \in [ALLOWED_MEM_VALUES -> ALLOWED_MEM_VALUES]:
                        user_buffer' = SeqOfNElements(data, PageSize)
                   /\ \E idx \in 1..PagesCount:
                        page_mem' = [status |-> "start_write", page_idx |-> idx]
             /\ pc' = [pc EXCEPT !["Client"] = "ResetTick"]
             /\ UNCHANGED << memory_pages, client_init, keys, keys_count, 
                             map_status, next_map_status, action, current_key, 
                             new_value, current_key_index, current_sector, 
                             current_sector_page, current_value_cell, 
                             map_command >>

client == ResetTick

PageMemTick == /\ pc["PageMem"] = "PageMemTick"
               /\ \/ /\ page_mem.status = "init"
                     /\ page_mem' = [page_mem EXCEPT !.status = "idle"]
                     /\ UNCHANGED <<memory_pages, user_buffer>>
                  \/ /\ page_mem.status = "idle"
                     /\ UNCHANGED <<memory_pages, user_buffer, page_mem>>
                  \/ /\ page_mem.status = "start_read"
                     /\ user_buffer' = [user_buffer EXCEPT ![1] = memory_pages[page_mem.page_idx][1]]
                     /\ page_mem' = [page_mem EXCEPT !.status = "read_tail"]
                     /\ UNCHANGED memory_pages
                  \/ /\ page_mem.status = "read_tail"
                     /\ user_buffer' =              SequencePart(user_buffer, 1, 1) \o
                                       SequencePart(memory_pages[page_mem.page_idx], 2, PageSize - 1)
                     /\ Assert(/\ Len(user_buffer') = PageSize
                               /\ memory_pages[page_mem.page_idx] = user_buffer', 
                               "Failure of assertion at line 107, column 9.")
                     /\ page_mem' = [page_mem EXCEPT !.status = "idle"]
                     /\ UNCHANGED memory_pages
                  \/ /\ page_mem.status = "start_write"
                     /\ memory_pages' = [memory_pages EXCEPT ![page_mem.page_idx][1] = user_buffer[1]]
                     /\ page_mem' = [page_mem EXCEPT !.status = "write_tail"]
                     /\ UNCHANGED user_buffer
                  \/ /\ page_mem.status = "write_tail"
                     /\ memory_pages' = [memory_pages EXCEPT ![page_mem.page_idx] =                                  <<user_buffer[1]>> \o
                                                                                    SequencePart(user_buffer, 2, PageSize - 1)]
                     /\ Assert(/\ Len(user_buffer) = PageSize
                               /\ memory_pages'[page_mem.page_idx] = user_buffer, 
                               "Failure of assertion at line 126, column 9.")
                     /\ page_mem' = [page_mem EXCEPT !.status = "idle"]
                     /\ UNCHANGED user_buffer
               /\ pc' = [pc EXCEPT !["PageMem"] = "PageMemTick"]
               /\ UNCHANGED << client_init, keys, keys_count, map_status, 
                               next_map_status, action, current_key, new_value, 
                               current_key_index, current_sector, 
                               current_sector_page, current_value_cell, 
                               map_command >>

page_mem_ == PageMemTick

MapTick == /\ pc["Map"] = "MapTick"
           /\ \/ /\ map_status = "init"
                 /\ UNCHANGED current_key_index
              \/ /\ map_status = "free"
                 /\ UNCHANGED current_key_index
              \/ /\ map_status = "find_current_key"
                 /\ Assert(Contains(keys, current_key), 
                           "Failure of assertion at line 161, column 7.")
                 /\ current_key_index' = IndexOf(keys, current_key)
           /\ pc' = [pc EXCEPT !["Map"] = "Done"]
           /\ UNCHANGED << memory_pages, user_buffer, client_init, page_mem, 
                           keys, keys_count, map_status, next_map_status, 
                           action, current_key, new_value, current_sector, 
                           current_sector_page, current_value_cell, 
                           map_command >>

map == MapTick

MapClientTick == /\ pc["MapClient"] = "MapClientTick"
                 /\ \/ /\ map_status = "free"
                       /\ UNCHANGED <<page_mem, map_status, next_map_status, action, current_key, new_value, current_sector_page>>
                    \/ /\ map_status = "free"
                       /\ \E key \in ALLOWED_MEM_VALUES:
                            \E increment \in ALLOWED_MEM_VALUES:
                              IF ~Contains(keys, increment) /\ keys_count = MAX_KEYS_COUNT
                                 THEN /\ TRUE
                                      /\ UNCHANGED << page_mem, map_status, 
                                                      next_map_status, action, 
                                                      current_key, new_value, 
                                                      current_sector_page >>
                                 ELSE /\ new_value' = increment
                                      /\ IF current_key /= key \/ keys_count = 0
                                            THEN /\ map_status' = "find_current_key"
                                                 /\ current_key' = key
                                                 /\ action' = "write_value"
                                                 /\ UNCHANGED << page_mem, 
                                                                 next_map_status, 
                                                                 current_sector_page >>
                                            ELSE /\ current_sector_page' = (current_sector_page + 1) % SECTOR_SIZE_PAGES
                                                 /\ page_mem' = [status |-> "read", page_idx |-> current_sector * SECTOR_SIZE_PAGES + current_sector_page']
                                                 /\ map_status' = "wait_page_mem"
                                                 /\ next_map_status' = "write_new_value"
                                                 /\ UNCHANGED << action, 
                                                                 current_key >>
                    \/ /\ map_status = "free"
                       /\ UNCHANGED <<page_mem, map_status, next_map_status, action, current_key, new_value, current_sector_page>>
                    \/ /\ map_status = "free"
                       /\ UNCHANGED <<page_mem, map_status, next_map_status, action, current_key, new_value, current_sector_page>>
                    \/ /\ map_status = "free"
                       /\ UNCHANGED <<page_mem, map_status, next_map_status, action, current_key, new_value, current_sector_page>>
                 /\ pc' = [pc EXCEPT !["MapClient"] = "Done"]
                 /\ UNCHANGED << memory_pages, user_buffer, client_init, keys, 
                                 keys_count, current_key_index, current_sector, 
                                 current_value_cell, map_command >>

map_client == MapClientTick

Next == reset \/ client \/ page_mem_ \/ map \/ map_client

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(reset)
        /\ WF_vars(client)

\* END TRANSLATION

PageMemStatusInvariant == page_mem.status \in {
  "init",
  "idle",
  "start_read",
  "read_tail",
  "start_write",
  "write_tail"
}

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


MapCommandInvariant == map_command \in {
  "no_command",
  "clear",
  "increment_value",
  "get_value",
  "replace_key",
  "update_value"
}

PageMemIndexesInvariant ==
  /\ page_mem.page_idx \in 1..PagesCount

====

