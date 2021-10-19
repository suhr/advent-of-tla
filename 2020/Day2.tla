---- MODULE Day2 ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Char

CONSTANTS min, max, sym, pass
ASSUME \E n \in Nat:
    /\ min \in [1..n -> Nat]
    /\ max \in [1..n -> Nat]
    /\ sym \in [1..n -> Char]
    /\ pass \in [1..n -> Seq(Char)]

Count(e, seq) == Cardinality({i \in 1..Len(seq) : seq[i] = e})
Valid(i)      == Count(sym[i], pass[i]) \in min[i]..max[i]
    
Goal == Cardinality({i \in 1..Len(pass) : Valid(i)})

====
