---- MODULE Day6 ----
EXTENDS Integers, FiniteSets

CONSTANTS Group, Person, Question
CONSTANTS pop, ans
ASSUME
    /\ pop \in [Group -> Person]
    /\ ans \in [Person -> Question]

Pick(S) == CHOOSE x \in S: TRUE

RECURSIVE SetReduce(_, _, _)
SetReduce(base, op(_,_), S) ==
    IF S = {} THEN base
    ELSE SetReduce(op(base, Pick(S)), op, S \ {Pick(S)})

GrAns(gr) == {a \in Question : \E p: p \in pop[gr] /\ a \in ans[p]}
AnsCount == {Cardinality(GrAns(g)) : g \in Group}

Goal == SetReduce(0, +, AnsCount)

====
