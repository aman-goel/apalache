------------------------------- MODULE TCommitUFO ------------------------------
\* benchmark: tla-tcommit

CONSTANT
    \* We define the set of all values of the sort SORT_RM,
    \* as we are quantifying over this sort.
    \* @type: Set(SORT_RM);
    RM

VARIABLES
  \* rmState[rm] is the state of resource manager RM.
  \* It is an uninterpreted non-Boolean function, which is fine in UFOL.
  \* @type: SORT_RM -> SORT_STATE;
  rmState

\* We do not need this definition in UFOL:
\*TPTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
(*  
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
 *) 

Init ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  \* working_OF_SORT_STATE is interpreted
  \* as a distinct constant 'working' of the sort SORT_STATE
  /\ rmState = [rm \in RM |-> "working_OF_SORT_STATE"]

canCommit == \A rm \in RM : \/ rmState[rm] = "prepared_OF_SORT_STATE"
                                   \/ rmState[rm] = "committed_OF_SORT_STATE"
  (*************************************************************************)
  (* True iff all RMs are in the "prepared" or "committed" state.          *)
  (*************************************************************************)

notCommitted == \A rm \in RM : rmState[rm] # "committed_OF_SORT_STATE" 
  (*************************************************************************)
  (* True iff neither no resource manager has decided to commit.           *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the RMs, and then    *)
(* define the complete next-state action of the specification to be the    *)
(* disjunction of the possible RM actions.                                 *)
(***************************************************************************)
Prepare(rm) == /\ rmState[rm] = "working_OF_SORT_STATE"
               /\ rmState' = [rmState EXCEPT ![rm] = "prepared_OF_SORT_STATE"]

Decide(rm)  == \/ /\ rmState[rm] = "prepared_OF_SORT_STATE"
                  /\ canCommit
                  /\ rmState' = [rmState EXCEPT ![rm] = "committed_OF_SORT_STATE"]
               \/ /\ \/ rmState[rm] = "working_OF_SORT_STATE"
                     \/ rmState[rm] = "prepared_OF_SORT_STATE"
                  /\ notCommitted
                  /\ rmState' = [rmState EXCEPT ![rm] = "aborted_OF_SORT_STATE"]

Next == \E rm \in RM : Prepare(rm) \/ Decide(rm)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
-----------------------------------------------------------------------------
TCSpec == Init /\ [][Next]_rmState
  (*************************************************************************)
  (* The complete specification of the protocol.                           *)
  (*************************************************************************)
-----------------------------------------------------------------------------

TCConsistent ==
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM :
       ~ /\ rmState[rm1] = "aborted_OF_SORT_STATE"
         /\ rmState[rm2] = "committed_OF_SORT_STATE"
==============================================================================

=============================================================================
