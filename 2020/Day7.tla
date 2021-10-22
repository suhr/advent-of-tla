---- MODULE Day7 ----
EXTENDS Integers, FiniteSets

CONSTANTS Bag, ShinyGold
ASSUME ShinyGold \in Bag

CONSTANT rules
ASSUME rules \in [Bag -> [Bag -> Nat]]

MinBy(S, le(_,_)) == CHOOSE x \in S: \A y \in S: le(x, y)
Trans(R, S) == \A x,y,z \in S: <<x, y>> \in R /\ <<y, z>> \in R => <<x, z>> \in R

ContainsRel ==
    LET B == Bag \times Bag
        I == {<<o, i>> \in B : rules[o][i] > 0}
    IN  MinBy({R \in SUBSET B : Trans(R, Bag) /\ I \subseteq R}, \subseteq)
ContainSG == {o \in Bag : <<o, ShinyGold>> \in ContainsRel}

Goal == Cardinality(ContainSG)

====
