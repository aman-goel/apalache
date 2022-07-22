---- MODULE lockserverUFO ----
\* benchmark: i4-lock-server

\* EXTENDS TLC, Naturals

\*
\* Simple lock server example.
\*
\* The system consists of a set of servers and a set of clients.
\* Each server maintains a single lock, which can be granted to a 
\* client if it currently owns that lock. 
\* 

CONSTANT
    \* @type: Set(S);
    Server,
    \* @type: Set(C);
    Client

\* CONSTANT
\*     \* @type: Str;
\*     Nil

VARIABLE
    \* @type: S -> Bool;
    semaphore,
    \* @type: <<C, S>> -> Bool;
    clientlocks

\* vars == <<semaphore, clientlocks>>

\* A client c requests a lock from server s.
Connect(c, s) == 
    \* The server must currently hold the lock.
    /\ semaphore[s] = TRUE
    \* The client obtains the lock of s.
    /\ clientlocks' = [clientlocks EXCEPT ![<<c, s>>] = TRUE]
    /\ semaphore' = [semaphore EXCEPT ![s] = FALSE]


\* A client c relinquishes the lock of server s.
Disconnect(c, s) ==
    \* The client must currently be holding the lock of s.
    /\ clientlocks[<<c, s>>] = TRUE
    \* The relinquishes the lock of s.
    /\ clientlocks' = [clientlocks EXCEPT ![<<c, s>>] = FALSE]
    /\ semaphore' = [semaphore EXCEPT ![s] = TRUE]
    
Init == 
    \* Initially each server holds its lock, and all clients hold 
    \* no locks.
    /\ semaphore = [s \in Server |-> TRUE]
    /\ clientlocks = [c \in Client, s \in Server |-> FALSE]

Next == 
    \/ \E c \in Client, s \in Server : Connect(c, s)
    \/ \E c \in Client, s \in Server : Disconnect(c, s)

\* NextUnchanged == UNCHANGED vars

\* TypeOK == 
\*     /\ semaphore \in [Server -> BOOLEAN]
\*     /\ clientlocks \in [Client \X Server -> BOOLEAN]

\* Two different clients cannot hold the lock of the same server simultaneously.
Inv == \A ci,cj \in Client : \A s \in Server : (clientlocks[<<ci, s>>] /\ clientlocks[<<cj, s>>]) => (ci = cj)

\* \* The inductive invariant.
\* Ind == 
\*     /\ TypeOK
\*     /\ Inv
\*     \* A client and server never hold the same lock at the same time.
\*     /\ \A c \in Client, s \in Server : (clientlocks[<<c, s>>] = TRUE) => ~semaphore[s]

====
