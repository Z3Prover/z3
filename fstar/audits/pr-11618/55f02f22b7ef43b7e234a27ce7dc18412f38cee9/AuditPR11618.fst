module AuditPR11618
open FStar.Real

(* Obligation 1: product kernels of Z3SortedRealProduct.fst, on the real values. *)
#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"
let product_positive (x y:real) : Lemma (requires x >. 0.0R /\ y >. 0.0R) (ensures x *. y >. 0.0R) = ()
let product_nonpositive (x y:real)
  : Lemma (requires (x >=. 0.0R /\ y <=. 0.0R) \/ (x <=. 0.0R /\ y >=. 0.0R)) (ensures x *. y <=. 0.0R) = ()
#pop-options

(* Obligation 2: Z3SortedRealOrder.lemma_subtract_zero. *)
let subtract_zero (x:real) : Lemma (x -. 0.0R == x) = ()

(* Obligation 3: rule_shape keeps th-lemma and erases other unlisted payloads;
   model rule_shape on a reduced rule type and prove idempotence and th-lemma preservation. *)
type rule = | Asserted | Unverified : string -> rule | Other : nat -> rule
let rule_shape (r:rule) : rule =
  if r = Unverified "th-lemma" then r else match r with
  | Asserted -> r
  | _ -> Unverified "payload-erased"
let shape_th_lemma () : Lemma (rule_shape (Unverified "th-lemma") == Unverified "th-lemma") = ()
let shape_idem (r:rule) : Lemma (rule_shape (rule_shape r) == rule_shape r) = ()
let shape_other (n:nat) : Lemma (rule_shape (Other n) == Unverified "payload-erased") = ()
