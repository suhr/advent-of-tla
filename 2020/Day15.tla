---- MODULE Day15 ----
EXTENDS Integers, Sequences

Max(S) == CHOOSE x \in S: \A y \in S: x >= y

CONSTANT init
ASSUME init \in Seq(Nat)

VARIABLE spoken

Dist == Len(spoken) - Max({i \in DOMAIN spoken : spoken[i] = spoken[Len(spoken)]})

Init == spoken = init
Next == spoken' = spoken \o <<Dist>>
Spec == Init /\ [][Next]_spoken

Goal(num) == <>(Len(spoken) = 2020 /\ spoken[2020] = num)

====
