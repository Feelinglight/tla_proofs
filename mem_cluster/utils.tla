---- MODULE utils ----
EXTENDS TLC, Integers, Sequences


\* Последовательности длины n, состоящая из одинаковых элементов element
SeqOfNElements(element, n) == [x \in 1..n |-> element]

\* Последовательности длины n, состоящая из рандомных элементов element
SeqOfNRandomElements(n, seed) == [x \in 1..n |-> RandomElement(seed)]

\* Часть последовательности seq, начиная с индекса start, длины n
SequencePart(seq, start, n) == [x \in 1..n |-> seq[start + x - 1]]

ReduceSequence(seq, op(_, _), acc) ==
  LET f[i \in 0..Len(seq)] ==
    IF i = 0 THEN acc
    ELSE op(f[i - 1], seq[i])
  IN f[Len(seq)]

\* Делает плоской последовательность последовательностей
\* <<<<1, 2, 3>>, <<4, 5, 6>> -> <<1, 2, 3, 4, 5, 6>>
FlatSubSequences(seq_of_seq) ==
  ReduceSequence(seq_of_seq, \o, <<>>)

====