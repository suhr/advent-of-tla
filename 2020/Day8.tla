---- MODULE Day8 ----
EXTENDS Integers, Sequences

Op == {"acc", "jmp", "nop"}

CONSTANT code
ASSUME code \in Seq(Op \times Int)

VARIABLES acc, ip, visited

vars == <<acc, ip, visited>>

Loop == {ip} \in visited

Init == ip = 1 /\ acc = 0 /\ visited = {}
Next == \E i \in Int:
    /\ ~Loop
    /\ visited' = visited \cup {ip}
    /\ \/ code[ip] = <<"acc", i>> /\ ip' = ip + 1 /\ acc' = acc + i
       \/ code[ip] = <<"jmp", i>> /\ ip' = ip + i
       \/ code[ip] = <<"nop", i>> /\ ip' = ip + 1
Spec == Init /\ [][Next]_vars

Goal(a) == <>(Loop /\ acc = a)    \* TLA+ does not allow CHOOSE here

====
