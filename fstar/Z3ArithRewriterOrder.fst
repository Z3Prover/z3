module Z3ArithRewriterOrder

(*
   Companion module to Z3ArithRewriter.fst: formalizes the comparison-operator
   identities from src/ast/rewriter/arith_rewriter.cpp that were left out of
   the first pass (mk_lt_core, mk_gt_core, the `m_eq2ineq` branch of
   mk_eq_core, the generic ite-over-comparison lifting shared by
   mk_le_ge_eq_core's three ite-hoisting branches, the to_int/comparison
   bridging rule, and the `is_bound` mod-range corollaries). Kept separate
   from Z3ArithRewriter.fst for the same verification-performance reasons
   documented there.
*)

open FStar.Real
open Z3ArithRewriter   // reuses `mod_range`

(* ----------------------------------------------------------------- *)
(* mk_lt_core / mk_gt_core : lt/gt expressed via not(le)               *)
(* ----------------------------------------------------------------- *)

/// mk_lt_core: (< a b) rewrites to (not (<= b a)).
let lt_as_not_le (a b:real) : Lemma ((a <. b) <==> ~(b <=. a)) = ()

/// mk_gt_core: (> a b) rewrites to (not (<= a b)).
let gt_as_not_le (a b:real) : Lemma ((a >. b) <==> ~(a <=. b)) = ()

(* ----------------------------------------------------------------- *)
(* mk_eq_core, m_eq2ineq branch : eq(a,b) = and(le(a,b), ge(a,b))      *)
(* ----------------------------------------------------------------- *)

/// Antisymmetry of the real order: a = b iff a <= b and b <= a.
let eq_as_ineqs (a b:real) : Lemma ((a == b) <==> (a <=. b /\ b <=. a)) = ()

(* ----------------------------------------------------------------- *)
(* mk_le_ge_eq_core's ite-hoisting branches : lifting a comparison     *)
(* through an ite is unconditionally valid (not just a numeral-folding *)
(* heuristic) -- the rewriter restricts it to the `ref_count == 1`     *)
(* case purely to control term blow-up, not because of a side         *)
(* condition on the identity itself.                                  *)
(* ----------------------------------------------------------------- *)

let ite_lift_le (c:bool) (t e k:real) : Lemma
  (((if c then t else e) <=. k) <==> (if c then (t <=. k) else (e <=. k))) =
  if c then () else ()

let ite_lift_ge (c:bool) (t e k:real) : Lemma
  (((if c then t else e) >=. k) <==> (if c then (t >=. k) else (e >=. k))) =
  if c then () else ()

let ite_lift_eq (c:bool) (t e k:real) : Lemma
  (((if c then t else e) == k) <==> (if c then (t == k) else (e == k))) =
  if c then () else ()

(* ----------------------------------------------------------------- *)
(* mk_le_ge_eq_core's to_int-bridging branch : the floor-comparison    *)
(* identities that justify rewriting `(<= (to_int t) n)` etc. purely   *)
(* in terms of `t`. to_int/to_real are modeled, as in                  *)
(* Z3ArithRewriterCast.fst, via an abstract embedding together with    *)
(* the two inequalities that characterize `to_int` as the floor of     *)
(* its argument, and the fact that `to_real` is order-preserving.      *)
(* ----------------------------------------------------------------- *)

assume val to_real : int -> real
assume val to_int : real -> int

/// Defining property of floor: to_real(to_int t) <= t < to_real(to_int t + 1).
assume val floor_spec (t:real) : Lemma
  (to_real (to_int t) <=. t /\ t <. to_real (to_int t + 1))

/// to_real is order-preserving (both non-strict and strict).
assume val to_real_mono_le (m n:int) : Lemma (requires m <= n) (ensures to_real m <=. to_real n)
assume val to_real_mono_lt (m n:int) : Lemma (requires m < n) (ensures to_real m <. to_real n)

/// mk_le_ge_eq_core's `is_to_int` branch, LE case:
/// (to_int t) <= n  <=>  t < to_real(n+1).
let to_int_le_iff (t:real) (n:int) : Lemma
  ((to_int t <= n) <==> (t <. to_real (n + 1))) =
  floor_spec t;
  if to_int t <= n then to_real_mono_le (to_int t + 1) (n + 1)
  else to_real_mono_le (n + 1) (to_int t)

/// mk_le_ge_eq_core's `is_to_int` branch, GE case:
/// (to_int t) >= n  <=>  t >= to_real(n).
let to_int_ge_iff (t:real) (n:int) : Lemma
  ((to_int t >= n) <==> (to_real n <=. t)) =
  floor_spec t;
  if to_int t >= n then to_real_mono_le n (to_int t)
  else to_real_mono_le (to_int t + 1) n

/// mk_le_ge_eq_core's `is_to_int` branch, EQ case:
/// (to_int t) = n  <=>  to_real(n) <= t < to_real(n+1).
let to_int_eq_iff (t:real) (n:int) : Lemma
  ((to_int t = n) <==> (to_real n <=. t /\ t <. to_real (n + 1))) =
  to_int_le_iff t n;
  to_int_ge_iff t n

(* ----------------------------------------------------------------- *)
(* `is_bound`'s mod-range corollaries : every one of the constant-     *)
(* folding shortcuts for `(mod x b) <= c` / `(mod x b) >= c` with a    *)
(* numeral `c` is a direct corollary of `0 <= mod x b < b`.            *)
(* ----------------------------------------------------------------- *)

/// (mod x b) >= 0 is always true for a positive modulus.
let mod_ge_zero_true (x b:int) : Lemma (requires b > 0) (ensures x % b >= 0) =
  mod_range x b

/// (mod x b) <= c is false whenever c < 0.
let mod_le_neg_false (x b c:int) : Lemma (requires b > 0 /\ c < 0) (ensures ~ (x % b <= c)) =
  mod_range x b

/// (mod x b) <= c is true whenever c >= b (the remainder is always < b).
let mod_le_ge_modulus_true (x b c:int) : Lemma (requires b > 0 /\ c >= b) (ensures x % b <= c) =
  mod_range x b

/// (mod x b) <= b - 1 is always true (the tightest such bound).
let mod_le_modulus_minus_one (x b:int) : Lemma (requires b > 0) (ensures x % b <= b - 1) =
  mod_range x b

/// (mod x b) >= c is false whenever c > b - 1, i.e. c >= b.
let mod_ge_too_large_false (x b c:int) : Lemma (requires b > 0 /\ c >= b) (ensures ~ (x % b >= c)) =
  mod_range x b

(* ----------------------------------------------------------------- *)
(* `is_separated`'s nonnegative-summand bound : if every non-numeral   *)
(* summand of a sum is known non-negative, the sum is bounded below    *)
(* by its numeral part -- the fact `is_separated` uses to certify      *)
(* `(<= (+ c x) k) = false` once `c > k`.                              *)
(* ----------------------------------------------------------------- *)

let nonneg_summand_le_false (c k x:int) : Lemma
  (requires x >= 0 /\ c > k) (ensures ~ (c + x <= k)) = ()

/// Dual case: if every non-numeral summand is known non-positive (the
/// `is_neg_poly`/`is_non_negative` combination `is_separated` uses for the
/// GE direction), the sum is bounded above by its numeral part.
let nonpos_summand_ge_false (c k x:int) : Lemma
  (requires x <= 0 /\ c < k) (ensures ~ (c + x >= k)) = ()
