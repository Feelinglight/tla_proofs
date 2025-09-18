---- MODULE utils ----
EXTENDS TLC, Integers, Sequences, SequencesExt


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
FlatSubSequences(seq_of_seq) == ReduceSequence(seq_of_seq, \o, <<>>)

Range(seq) == {seq[i]: i \in DOMAIN seq}

Min(set) == CHOOSE x \in set: \A el \in set: x <= el

\* Возвращает индекс элемента в последовательности. От 0 до Len(seq) - 1
\* Если элемент не найден, то возвращает default
IndexOrDefault(seq, elem, default) ==
  IF Contains(seq, elem) THEN
    CHOOSE i \in 0..(Len(seq) - 1): seq[i + 1] = elem
  ELSE
    default

\* Возвращает индекс элемента в последовательности. От 0 до Len(seq) - 1
\* Возращаемое значение - функция вида [result, index].
\* Если элемент есть в последовательности, то результат - TRUE, иначе FALSE
IndexAndResult(seq, elem) ==
  LET
    result == Contains(seq, elem)
  IN
    IF Contains(seq, elem) THEN
      [found |-> result, index |-> CHOOSE i \in 0..(Len(seq) - 1): seq[i + 1] = elem]
    ELSE
      [found |-> result, index |-> 0]

====
