---- MODULE Day14 ----
EXTENDS Integers

Len(arr) == CHOOSE n \in Nat: DOMAIN arr = 0..n-1
Drop(n, arr) == {i \in 0..Len(arr)-n-1 : arr[i-n]}

RECURSIVE FoldLeft(_, _, _)
FoldLeft(base, op(_,_), arr) ==
    IF Len(arr) = 0 THEN base
    ELSE FoldLeft(op(base, arr[0]), op, Drop(1, arr))

I == 0..(2^36 - 1)

CONSTANT mask, program
ASSUME    \* Also assume no big-endian nonsense
    /\ \E B \in SUBSET 0..35: mask \in [B -> {0, 1}]
    /\ \E n \in Nat: program \in [0..n-1 -> I \times I]

Repr(b, n)  == b \in [0..35 -> {0, 1}] /\ n = FoldLeft(0, +, [i \in 0..35 |-> 2^b[i]])
Apply(m, b) == [i \in DOMAIN b |-> IF i \in DOMAIN m THEN m[i] ELSE b[i]]
Mask(n)     == CHOOSE k: \E b: Repr(b, n) /\ Repr(Apply(mask, b), k)

Memory ==
    LET Write(m, op) == [m EXCEPT ![op[1]] = Mask(op[2])]
    IN FoldLeft([i \in I |-> 0], Write, program)

Goal == FoldLeft(0, +, Memory)

====
