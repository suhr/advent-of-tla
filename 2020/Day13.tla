---- MODULE Day13 ----
EXTENDS Integers

CONSTANTS start, Bus
ASSUME start \in Nat /\ Bus \subseteq Nat \ {0}

MinBy(S, le(_,_)) == CHOOSE x \in S: \A y \in S: le(x, y)

Departs == {<<b, b*n>> : <<b, n>> \in Bus \times Nat}
Earliest == MinBy({d \in Departs : d[2] >= start}, LAMBDA dx, dy: dx[2] <= dy[2])

Goal == Earliest[1] * (Earliest[2] - start)

====
