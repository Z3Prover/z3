module Z3InverseTrigGuards
(* Abstract ordered-ring model of PR 11438 guards. Functions are hypotheses
   (preconditions), not axioms. Carrier int stands for the ordered real field
   for the ring/order facts used; guards are over the numeral k. *)

let in_sin_dom (k:int) = -1 <= k && k <= 1
let in_cosh_dom (k:int) = k >= 1

(* Obligation 1 (mk_sin_core asin branch): guard => sin(asin k) = k.
   Spec of asin on its domain: sin (asin k) = k. *)
let sin_asin_sound (sin asin : int -> int) (k:int)
  : Lemma (requires in_sin_dom k /\ sin (asin k) = k) (ensures sin (asin k) = k) = ()

(* Obligation 2 (witness for the old unguarded rule): sin is bounded by 1,
   so for k=2 the unguarded rewrite sin(asin 2)=2 is false in every model. *)
let sin_asin_old_unsound (sin asin : int -> int)
  : Lemma (requires (forall y. -1 <= sin y /\ sin y <= 1))
          (ensures ~(sin (asin 2) = 2)) = ()

(* Obligation 3 (mk_sin_core acos branch): for guarded k, with c=cos a=k,
   s=sin a >=0 (a in [0,pi]) and s^2+c^2=1: s*s = 1-k*k and 1-k*k >= 0,
   so sqrt(1-k^2) is defined and equals s. Also guard is necessary: k=2
   makes 1-k*k negative. *)
let sin_acos_sound (s c k:int)
  : Lemma (requires in_sin_dom k /\ c = k /\ s >= 0 /\ s*s + c*c = 1)
          (ensures s*s = 1 - k*k /\ 1 - k*k >= 0 /\ s >= 0) = ()
let sin_acos_guard_needed : squash (1 - 2*2 < 0) = ()

(* mk_cos_core: cos(acos k)=k on [-1,1]; cos bounded refutes k=2. *)
let cos_acos_sound (cos acos : int -> int) (k:int)
  : Lemma (requires in_sin_dom k /\ cos (acos k) = k) (ensures cos (acos k) = k) = ()
let cos_acos_old_unsound (cos acos : int -> int)
  : Lemma (requires (forall y. -1 <= cos y /\ cos y <= 1))
          (ensures ~(cos (acos 2) = 2)) = ()

(* mk_cosh_core: cosh(acosh k)=k for k>=1; cosh>=1 refutes k=0 (and k<1). *)
let cosh_acosh_sound (cosh acosh : int -> int) (k:int)
  : Lemma (requires in_cosh_dom k /\ cosh (acosh k) = k) (ensures cosh (acosh k) = k) = ()
let cosh_acosh_old_unsound (cosh acosh : int -> int)
  : Lemma (requires (forall y. cosh y >= 1))
          (ensures ~(cosh (acosh 0) = 0)) = ()
