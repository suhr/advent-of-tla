---- MODULE Day9 ----
EXTENDS Integers, Sequences

CONSTANT data
ASSUME data \in Seq(Nat) /\ Len(data) > 25

Min(S) == CHOOSE x \in S: \A y \in S: x <= y

Valid(i) == \E n, k \in DOMAIN data:
    /\ i-n \in 0..24 /\ i-k \in 0..24
    /\ data[n] /= data[k]
    /\ data[i] = data[n] + data[k]
Invalid == {i \in 26..Len(data) : ~Valid(i)}

Goal == data[Min(Invalid)]

====
