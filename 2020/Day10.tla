---- MODULE Day10 ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS AdapterCount, jolts
ASSUME AdapterCount \in Nat /\ jolts \in [1..AdapterCount -> Nat]

Max(S) == CHOOSE x \in S: \A y \in S: x >= y

Output == 3 + Max({jolts[i] : i \in DOMAIN jolts})
Point == {<<i, j>> \in Nat \times Nat :
    \/ i = 0              /\ j = 0
    \/ i \in DOMAIN jolts /\ j = jolts[i]
    \/ i = Len(jolts) + 1 /\ j = Output
}
ConnRel ==
    LET P == Point \times Point
        B == {<<px, py>> \in P : py[2] - px[2] \in 0..3}
    IN {<<px, pz>> \in P : \E py \in Point: {<<px, py>>, <<py, pz>>} \subseteq B}
Chain == CHOOSE ch \in [1..Cardinality(Point) -> Point]:
    \A i \in 2..Len(ch): <<ch[i-1], ch[i]>> \in ConnRel
Count(dj) == Cardinality({i \in 2..Len(Chain) : Chain[i]-Chain[i-1] = dj})

Goal == Count(1) * Count(3)

====
