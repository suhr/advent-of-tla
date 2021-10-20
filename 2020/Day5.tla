---- MODULE Day5 ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANT passes
ASSUME passes \in Seq([1..7 -> {"F", "B"}] \times [1..3 -> {"L", "R"}])

Drop(n, seq) == SubSeq(seq, n+1, Len(seq))
Max(S) == CHOOSE x \in S: \A y \in S: x >= y

RECURSIVE FoldLeft(_, _, _)
FoldLeft(base, op(_,_), seq) ==
    IF Len(seq) = 0 THEN base
    ELSE FoldLeft(op(base, seq[1]), op, Drop(1,seq))

Split(r, is_upper) ==
    IF is_upper THEN <<r[1] + (r[2]-r[1]) \div 2, r[2]>>
    ELSE <<r[1], r[1] + (r[2]-r[1]) \div 2>>
YPos(seq) == FoldLeft(<<0, 128>>,LAMBDA r, y: Split(r, y = "B"), seq)[1]
XPos(seq) == FoldLeft(<<0, 8>>,  LAMBDA r, y: Split(r, y = "R"), seq)[1]
PassId(i) == 8*YPos(passes[i][1]) + XPos(passes[i][2])

Goal == Max({PassId(i) : i \in 1..Len(passes)})

====
