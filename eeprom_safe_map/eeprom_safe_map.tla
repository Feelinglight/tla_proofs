---- MODULE eeprom_safe_map ----
EXTENDS TLC, Integers, utils, SequencesExt, FiniteSets

CONSTANTS PagesCount, PageSize, NULL, INIT_MEM_VALUE, ALLOWED_MEM_VALUES

ASSUME PagesCount \in Nat \ {0}
ASSUME PageSize \in Nat \ {0}
ASSUME PageSize > 1

\* 0 и 1 используются под состояние чексуммы
ASSUME INIT_MEM_VALUE \in Nat \ {0}
ASSUME ALLOWED_MEM_VALUES \subseteq (Nat \ {0, 1})


(*--algorithm mem_cluster
variables
  \* read write
  memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)],
  user_buffer = SeqOfNElements(INIT_MEM_VALUE, PageSize),

  client_init = TRUE,

  page_mem = [status |-> "idle", page_idx |-> 1];


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

end algorithm; *)


\* BEGIN TRANSLATION (chksum(pcal) = "8b43f3bc" /\ chksum(tla) = "2133ac27")
\* Label ResetTick of process reset at line 29 col 5 changed to ResetTick_
\* Process page_mem at line 66 col 1 changed to page_mem_
VARIABLES memory_pages, user_buffer, client_init, page_mem

vars == << memory_pages, user_buffer, client_init, page_mem >>

ProcSet == {"Reset"} \cup {"Client"} \cup {"PageMem"}

Init == (* Global variables *)
        /\ memory_pages = [page \in 1..PagesCount |-> SeqOfNElements(INIT_MEM_VALUE, PageSize)]
        /\ user_buffer = SeqOfNElements(INIT_MEM_VALUE, PageSize)
        /\ client_init = TRUE
        /\ page_mem = [status |-> "idle", page_idx |-> 1]

reset == /\ \/ /\ page_mem' = [page_mem EXCEPT !.status = "init"]
            \/ /\ TRUE
               /\ UNCHANGED page_mem
         /\ UNCHANGED << memory_pages, user_buffer, client_init >>

client == /\ \/ /\ page_mem.status = "idle"
                /\ user_buffer' = SeqOfNElements(INIT_MEM_VALUE, PageSize)
                /\ \E idx \in 1..PagesCount:
                     page_mem' = [status |-> "start_read", page_idx |-> idx]
             \/ /\ page_mem.status = "idle"
                /\ \E data \in [ALLOWED_MEM_VALUES -> ALLOWED_MEM_VALUES]:
                     user_buffer' = SeqOfNElements(data, PageSize)
                /\ \E idx \in 1..PagesCount:
                     page_mem' = [status |-> "start_write", page_idx |-> idx]
          /\ UNCHANGED << memory_pages, client_init >>

page_mem_ == /\ \/ /\ page_mem.status = "init"
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
                             "Failure of assertion at line 92, column 9.")
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
                             "Failure of assertion at line 111, column 9.")
                   /\ page_mem' = [page_mem EXCEPT !.status = "idle"]
                   /\ UNCHANGED user_buffer
             /\ UNCHANGED client_init

Next == reset \/ client \/ page_mem_

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

PageMemIndexesInvariant ==
  /\ page_mem.page_idx \in 1..PagesCount

====

