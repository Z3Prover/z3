module AuditRealProduct
open FStar.Real
#push-options "--using_facts_from 'Prims FStar.Real' --fuel 0 --ifuel 0"
let positive_product (x y:real) : Lemma (requires x >. 0.0R /\ y >. 0.0R) (ensures x *. y >. 0.0R) = ()
let nonpositive_product (x y:real)
  : Lemma (requires (x >=. 0.0R /\ y <=. 0.0R) \/ (x <=. 0.0R /\ y >=. 0.0R)) (ensures x *. y <=. 0.0R) = ()
(* if both factors' signs are entailed and the product is also entailed to be the opposite, facts are contradictory *)
let contradiction_pos (x y p:real)
  : Lemma (requires x >. 0.0R /\ y >. 0.0R /\ p == x *. y /\ p <=. 0.0R) (ensures False) = ()
let contradiction_nonpos (x y p:real)
  : Lemma (requires ((x >=. 0.0R /\ y <=. 0.0R) \/ (x <=. 0.0R /\ y >=. 0.0R)) /\ p == x *. y /\ p >. 0.0R) (ensures False) = ()
#pop-options
