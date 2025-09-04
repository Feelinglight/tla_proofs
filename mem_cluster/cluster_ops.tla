---- MODULE cluster_ops ----
EXTENDS TLC, Integers, Sequences, utils

get_half_clusters_count(pages_count, page_size, cluster_size) ==
  (pages_count * page_size) \div cluster_size

\* Смещение первого полукластера кластера cluster_idx в плоском массиве памяти
get_first_half_cluster_offset(cluster_idx, pages_per_half_cluster) ==
  2 * cluster_idx * pages_per_half_cluster

\* Смещение второго полукластера кластера cluster_idx в плоском массиве памяти
get_second_half_cluster_offset(cluster_idx, pages_per_half_cluster) ==
  (2 * cluster_idx + 1) * pages_per_half_cluster

\* Возвращает содержимое полукластеров будет представлено в плоском виде, т. е. не как
\* последовательность страниц page_mem, а как их объединение в одну последовательность
first_half_cluster_content(memory_pages, cluster_idx, pages_per_half_cluster) ==
  FlatSubSequences(
    SequencePart(
      memory_pages,
      get_first_half_cluster_offset(cluster_idx, pages_per_half_cluster) + 1,
      pages_per_half_cluster
    )
  )

second_half_cluster_content(memory_pages, cluster_idx, pages_per_half_cluster) ==
  FlatSubSequences(
    SequencePart(
      memory_pages,
      get_second_half_cluster_offset(cluster_idx, pages_per_half_cluster) + 1,
      pages_per_half_cluster
    )
  )

====


