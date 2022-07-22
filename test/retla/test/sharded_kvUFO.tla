---- MODULE sharded_kvUFO ----
\* TODO

CONSTANTS
    \* @type: Set(K);
    Key,
    \* @type: Set(V);
    Value,
    \* @type: Set(N);
    Node,
    \* @type: V;
    Nil,
    \* @type: N;
    start

\* The key-value store state on each node.
VARIABLE
    \* @type: <<N, K>> -> V;
    table

\* The set of keys owned by each node.
VARIABLE
    \* @type: <<N, K>> -> Bool;
    owner

\* The set of active transfer messages.
VARIABLE
    \* @type: <<N, K, V>> -> Bool;
    transfer_msg

vars == <<table, owner, transfer_msg>>

Reshard(k,v,n_old,n_new) ==
    /\ v # Nil
    /\ table[<<n_old,k>>] = v
    /\ table' = [table EXCEPT ![<<n_old,k>>] = Nil]
    /\ owner' = [owner EXCEPT ![<<n_old,k>>] = FALSE]
    /\ transfer_msg' = [transfer_msg EXCEPT ![<<n_new,k,v>>] = TRUE]

RecvTransferMsg(n, k, v) ==
    /\ v # Nil
    /\ transfer_msg[<<n,k,v>>]
    /\ transfer_msg' = [transfer_msg EXCEPT ![<<n,k,v>>] = FALSE]
    /\ table' = [table EXCEPT ![<<n,k>>] = v]
    \* Become the owner of this key.
    /\ owner' = [owner EXCEPT ![<<n,k>>] = TRUE]

Put(n, k, v) == 
    /\ v # Nil
    /\ owner[<<n,k>>]
    /\ table' = [table EXCEPT ![<<n,k>>] = v]
    /\ UNCHANGED <<owner, transfer_msg>>

Next == 
    \/ \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
    \/ \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
    \/ \E n \in Node, k \in Key, v \in Value : Put(n,k,v)

Init == 
    /\ table = [n \in Node, k \in Key |-> Nil]
    \* Each node owns some subset of keys, and different nodes
    \* can't own the same key.
    /\ owner = [n \in Node, k \in Key |-> (n = start)]
    /\ \A i,j \in Node : \A k \in Key : (owner[<<i,k>>] /\ owner[<<j,k>>]) => (i=j)
    /\ transfer_msg = [n \in Node, k \in Key, v \in Value |-> FALSE]

\* TypeOK ==
\*     /\ table \in [Node -> [Key -> Value \cup {Nil}]]
\*     /\ owner \in [Node -> SUBSET Key]
\*     /\ transfer_msg \in SUBSET (Node \times Key \times Value)


\* Keys unique.
Safety == 
    \A n1,n2 \in Node, k \in Key, v1,v2 \in Value : 
        (table[<<n1,k>>]=v1 /\ table[<<n2,k>>]=v2 /\ (v1 # Nil) /\ (v2 # Nil)) => (n1=n2 /\ v1=v2)

====
