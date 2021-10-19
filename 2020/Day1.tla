---- MODULE Day1 ----
EXTENDS Integers

CONSTANT entities
ASSUME \E n \in Nat: entities \in [1..n -> Nat]

Goal ==
    LET p == CHOOSE <<i, j>>: entities[i]+entities[j] = 2020
    IN entities[p[1]]*entities[p[2]]

====
