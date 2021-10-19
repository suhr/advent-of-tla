---- MODULE Day3 ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANT map
ASSUME \E i, j \in Nat:
    map \in [(1..i) \times (1..j) -> {".", "#"}]

Shape(seq) == CHOOSE <<i, j>>: DOMAIN seq = (1..i) \times (1..j)

FullMap == [<<i, j>> \in DOMAIN map |-> map[<<1 + ((i-1) % Shape(map)[1]), j>>]]
Slope   == [i \in 1..Shape(map)[2]  |-> FullMap[<<1 + 3*i, 1 + i>>]]

Goal == Cardinality({i \in Len(Slope) : Slope[i] = "#"})

====
