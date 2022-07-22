---- MODULE simple_decentralized_lockUFO ----
\* benchmark: ex-simple-decentralized-lock

EXTENDS TLC

CONSTANT
    \* @type: Set(N);
    Node

VARIABLES
    \* @type: <<N, N>> -> Bool;
    message,
    \* @type: N -> Bool;
    has_lock

vars == <<message, has_lock>>

Send(src, dst) ==
    /\ has_lock[src]
    /\ message' = [message EXCEPT ![<<src, dst>>] = TRUE]
    /\ has_lock' = [has_lock EXCEPT ![src] = FALSE]

Recv(src, dst) ==
    /\ message[<<src, dst>>]
    /\ message' = [message EXCEPT ![<<src, dst>>] = FALSE]
    /\ has_lock' = [has_lock EXCEPT ![dst] = TRUE]

Next ==
    \/ \E src,dst \in Node : Send(src,dst)
    \/ \E src,dst \in Node : Recv(src,dst)

NextUnchanged == UNCHANGED vars

Init ==
    \E start \in Node :
        /\ message = [src \in Node, dst \in Node |-> FALSE]
        /\ has_lock = [n \in Node |-> (n = start)]

\* Two nodes can't hold lock at once.
Inv == \A x,y \in Node : (has_lock[x] /\ has_lock[y]) => (x = y)

====
