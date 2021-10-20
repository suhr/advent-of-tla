---- MODULE Day7 ----
EXTENDS Integers, FiniteSets

CONSTANTS Bag, ShinyGold
ASSUME ShinyGold \in Bag

CONSTANT rules
ASSUME rules \in [Bag -> [Bag -> Nat]]

ContainsRel ==
    LET B == {<<o, i>> \in Bag \times Bag : rules[o][i] > 0}
    IN {<<o, i>> \in Bag \times Bag : \E m: {<<o, m>>, <<m, i>>} \subseteq B}
ContainSG == {o \in Bag : <<o, ShinyGold>> \in ContainsRel}

Goal == Cardinality(ContainSG)

====
