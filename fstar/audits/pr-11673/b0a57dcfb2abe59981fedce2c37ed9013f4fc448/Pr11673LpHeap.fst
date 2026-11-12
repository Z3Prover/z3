module Pr11673LpHeap
(* Model of lar_solver::maximize_term cancel path (head b0a57dc).
   Columns are nat indices; x gives each column's value, lo/hi its bounds.
   heap models m_inf_heap as a membership predicate. *)

type status = | OPTIMAL | UNBOUNDED | CANCELLED | FEASIBLE

let feasible_col (x lo hi: nat -> int) (j: nat) : bool = lo j <= x j && x j <= hi j

(* invariant the solver relies on: heap contains exactly the infeasible columns *)
let heap_inv (x lo hi: nat -> int) (heap: nat -> bool) : prop =
  forall (j:nat). heap j <==> not (feasible_col x lo hi j)

let all_feasible (x lo hi: nat -> int) : prop = forall (j:nat). feasible_col x lo hi j

let empty_heap : nat -> bool = fun _ -> false

(* O1: after restore_x of a feasible backup and clear_inf_heap, the invariant holds
   (the SASSERT precondition at maximize_term entry says the backup is feasible). *)
let o1 (bk lo hi: nat -> int)
  : Lemma (requires all_feasible bk lo hi) (ensures heap_inv bk lo hi empty_heap) = ()

(* O2 (refutation of the pre-PR behaviour): restore without clear can leave a stale
   heap entry. Concrete witness: column 0, bounds [0,1], restored value 0, stale heap {0}. *)
let w_x : nat -> int = fun _ -> 0
let w_lo : nat -> int = fun _ -> 0
let w_hi : nat -> int = fun _ -> 1
let w_heap : nat -> bool = fun j -> j = 0
let o2 () : Lemma (all_feasible w_x w_lo w_hi /\ ~(heap_inv w_x w_lo w_hi w_heap)) =
  assert (w_heap 0 = true);
  assert (feasible_col w_x w_lo w_hi 0 = true)

(* O3: weakened SASSERT. On the path where maximize_term_on_tableau returns true,
   st is neither UNBOUNDED nor CANCELLED, so the weakened assertion is exactly the
   original feasibility assertion. *)
let assertion_new (st: status) (feas: bool) : bool = st = CANCELLED || feas
let returns_true (st: status) : bool = not (st = UNBOUNDED || st = CANCELLED)
let o3 (st: status) (feas: bool)
  : Lemma (returns_true st ==> (assertion_new st feas <==> feas)) = ()
