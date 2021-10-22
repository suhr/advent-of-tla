---- MODULE Day12 ----
EXTENDS Integers, Sequences

Abs(n)  == CHOOSE a \in {n, -n}: a >= 0
Inv(f)  == CHOOSE g: \A x \in DOMAIN f: g[f[x]] = x
Fun(gr) == [x \in {p[1] : p \in gr} |-> CHOOSE y: <<x, y>> \in gr]

Add(ax, ay) == [i \in DOMAIN ax |-> ax[i] + ay[i]]
Mul(a, v)   == [i \in DOMAIN a  |-> a[i] + v]

Op == {"N", "S", "E", "W", "L", "R", "F"}

CONSTANT ins
ASSUME ins \in Seq(Op \times Nat)

VARIABLES pos, dir, ip
vars == <<pos, dir, ip>>

Rot == Fun({
    << <<1, 0>>,  <<0, 1>>  >>,
    << <<0, 1>>,  <<-1, 0>> >>,
    << <<-1, 0>>, <<0, -1>> >>,
    << <<0, -1>>, <<1, 0>>  >>
})

Init == pos = <<0, 0>> /\ dir = <<1, 0>> /\ ip = 1
Next ==
    /\ ip \in DOMAIN ins /\ ip' = ip + 1
    /\ \/ ins[ip][1] = "N" /\ pos' = Add(pos, <<0, ins[ip][2]>>)    /\ dir' = dir
       \/ ins[ip][1] = "S" /\ pos' = Add(pos, <<0, -ins[ip][2]>>)   /\ dir' = dir
       \/ ins[ip][1] = "W" /\ pos' = Add(pos, <<-ins[ip][2], 0>>)   /\ dir' = dir
       \/ ins[ip][1] = "E" /\ pos' = Add(pos, <<ins[ip][2], 0>>)    /\ dir' = dir
       \/ ins[ip][1] = "L" /\ pos' = pos                            /\ dir' = Rot[dir]
       \/ ins[ip][1] = "R" /\ pos' = pos                            /\ dir' = Inv(Rot)[dir]
       \/ ins[ip][1] = "F" /\ pos' = Add(pos, Mul(dir, ins[ip][2])) /\ dir' = dir
Spec == Init /\ [][Next]_vars

Goal(dist) == <>(ip \notin DOMAIN ins /\ dist = Abs(pos[1]) + Abs(pos[2]))

====
