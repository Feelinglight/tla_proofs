---- MODULE cluster_ops ----
EXTENDS TLC, Integers, Sequences, utils, FiniteSets, SequencesExt

get_half_clusters_count(pages_count, page_size, cluster_size) ==
  (pages_count * page_size) \div cluster_size

\* Первая страница полукластера half_cluster_idx в кластере cluster_idx
\* cluster_idx с 0
\* half_cluster_idx 1 или 2
\* Return с 0
get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, half_cluster_idx) ==
  IF half_cluster_idx \in {1, 2} THEN
    (2 * cluster_idx + half_cluster_idx - 1) * pages_per_half_cluster
  ELSE
    Assert(half_cluster_idx \in {1, 2}, "Индекс полукластера должен быть 1 или 2")

\* Возвращает содержимое полукластеров будет представлено в плоском виде, т. е. не как
\* последовательность страниц page_mem, а как их объединение в одну последовательность
\* cluster_idx с 0
first_half_cluster_content(memory_pages, cluster_idx, pages_per_half_cluster) ==
  FlatSubSequences(
    SequencePart(
      memory_pages,
      get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, 1) + 1,
      pages_per_half_cluster
    )
  )

second_half_cluster_content(memory_pages, cluster_idx, pages_per_half_cluster) ==
  FlatSubSequences(
    SequencePart(
      memory_pages,
      get_half_cluster_start_page(cluster_idx, pages_per_half_cluster, 2) + 1,
      pages_per_half_cluster
    )
  )

\* Возвращает индекс первого, либо второго полукластера кластера cluster_idx
\* cluster_idx с 0
\* half_cluster_idx 1 или 2
\* Return с 1
get_half_cluster_idx(cluster_idx, half_cluster_idx) ==
  IF half_cluster_idx \in {1, 2} THEN
    2 * cluster_idx + half_cluster_idx
  ELSE
    Assert(half_cluster_idx \in {1, 2}, "Индекс полукластера должен быть 1 или 2")


\* Возвращает TRUE если crc данных в полукластере валидны, иначе FALSE
\* crc валидна, если все числа в полукластере одинаковые
\* cluster_idx с 0
\* half_cluster_idx 1 или 2
half_cluster_crc_ok(buffer, cluster_size, half_cluster_idx) ==
  IF half_cluster_idx \in {1, 2} THEN
    LET
      half_cluster_start == IF half_cluster_idx = 1 THEN 1 ELSE cluster_size + 1
    IN
      Cardinality(ToSet(SequencePart(buffer, half_cluster_start, cluster_size - 1))) = 1
  ELSE
    Assert(half_cluster_idx \in {1, 2}, "Индекс полукластера должен быть 1 или 2")

  \* idx \in 0..(clusters_count - 1) IN idx

        \* with idx \in 0..(clusters_count - 1) do
        \*   cluster_idx := idx;
        \* end with;


====


