module FiniteSetEqGuard
(* Model of the arity guard in finite_set_simplifier::rw_cfg::reduce_app (head a6faede1, lines 212-224).
   Not a model of rewriting itself: the filter/bounded branch is abstracted as `fires`. *)

type branch = | EqRewrite | Fallthrough

let old_guard (is_eq: bool) = is_eq
let new_guard (n: nat) (is_eq: bool) = n = 2 && is_eq

(* in-bounds reads of args[i], args[1-i] for i in {0,1} *)
let reads_in_bounds (n: nat) (i: nat{i < 2}) = i < n && (1 - i) < n

(* O1: whenever the new guard holds, every args[] access in the loop is in bounds. *)
let o1 (n: nat) (is_eq: bool) (i: nat{i < 2})
  : Lemma (requires new_guard n is_eq) (ensures reads_in_bounds n i) = ()

(* O2: old behavior is preserved for binary applications (guards agree). *)
let o2 (is_eq: bool) : Lemma (new_guard 2 is_eq == old_guard is_eq) = ()

(* O3: the old guard admitted out-of-bounds reads exactly when n<2 (witness n=1, i=1 -> args[0] ok, args[1-0]=args[1] OOB). *)
let o3 () : Lemma (old_guard true /\ ~(reads_in_bounds 1 0)) = ()
let o3b () : Lemma (~(new_guard 1 true)) = ()
