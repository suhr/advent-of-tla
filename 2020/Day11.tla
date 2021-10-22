---- MODULE Day11 ----
EXTENDS Integers, FiniteSets

Tile == {".", "L", "#"}

CONSTANTS w, h, inital
ASSUME {w, h} \subseteq Nat /\ inital \in [(1..w) \times (1..h) -> Tile]

VARIABLE tiles

Shift(arr, d) == [x \in DOMAIN arr |->
    IF <<x[1]+d[1], x[2]+d[2]>> \in DOMAIN arr
    THEN arr[<<x[1]+d[1], x[2]+d[2]>>]
    ELSE "."
]

AdjTiles(x) == {<<d, Shift(tiles, d)[x]>> : d \in (-1..1) \times (-1..1) \ {<<0, 0>>}}
OccCount(x) == Cardinality({t \in AdjTiles(x) : t[2] = "#"})

Init == tiles = inital
Next == \A x \in DOMAIN tiles:
    \/ tiles[x] = "L" /\ OccCount(x) = 0  /\ tiles' = [tiles EXCEPT ![x] = "#"]
    \/ tiles[x] = "#" /\ OccCount(x) >= 4 /\ tiles' = [tiles EXCEPT ![x] = "L"]
Spec == Init /\ [Next]_tiles

Goal(count) == \E ts:
    /\ <>[](tiles = ts)
    /\ count = Cardinality({x \in DOMAIN ts : ts[x] = "#"})

====
