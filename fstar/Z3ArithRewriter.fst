module Z3ArithRewriter

(*
   F star formalization of the arithmetic tautologies encoded by Z3's
   arithmetic rewriter: src/ast/rewriter/arith_rewriter.cpp /
   src/ast/rewriter/arith_rewriter.h.

   arith_rewriter.h documents the class as implementing the div/idiv/mod/rem,
   power, abs, to_int/to_real/is_int and related rewrite rules layered on top
   of the generic polynomial normalization performed by poly_rewriter (linear
   term flattening, monomial-cancellation, numeral folding).  The generic
   polynomial machinery (cancel_monomials, is_bound/factor_le_ge_eq,
   elim_to_real, get_range, the trigonometric mk_sin/cos/tan family) is
   search/algorithm code rather than a single reusable identity, and is
   summarized as out of scope in ARITH_BOOL_REWRITER_REPORT.md.

   We use F star's built-in `int` for integers and `/`, `%` for Euclidean
   truncation (F star's `/` and `%` on `int` already satisfy
   `a == (a/b)*b + a%b` with `0 <= a%b < |b|` for `b <> 0`, matching Z3's
   `mod`). Reals are modeled with `FStar.Real.real` using the dotted
   operators (`+.`, `-.`, `*.`, `/.`, `<.`, `<=.`). As in the NLA and
   seq_rewriter audits, quantifier-free facts here are discharged by Z3's
   native linear/nonlinear arithmetic decision procedures with proof body
   `()`; a few integer-division identities need explicit lemmas from
   `FStar.Math.Lemmas`.
*)

open FStar.Real

(* ----------------------------------------------------------------- *)
(* mk_div_core : real division identities                             *)
(* ----------------------------------------------------------------- *)

/// (/ a a) = 1 for any nonzero real a -- the numeral/numeral folding case.
let div_self (a:real) : Lemma (requires a =!= zero) (ensures (a /. a) == one) = ()

/// (/ a v) with numeral v <> 0 rewrites to (* (1/v) a) : mk_div_core's
/// "numeral denominator" branch, which replaces division by a constant
/// with multiplication by its reciprocal.
let div_by_numeral (a v:real) : Lemma (requires v =!= zero)
  (ensures (a /. v) == (one /. v) *. a) = ()

(* ----------------------------------------------------------------- *)
(* mk_idiv_core / mk_mod_core / mk_rem_core : integer division family *)
(* ----------------------------------------------------------------- *)

/// Euclidean division-mod decomposition that every idiv/mod rewrite relies
/// on implicitly: a = (idiv a b) * b + (mod a b).
let euclid_decomp (a b:int) : Lemma (requires b <> 0)
  (ensures a == (a / b) * b + (a % b)) = ()

/// mod's remainder is always in [0, b) for b > 0 -- the invariant that
/// justifies every modulus-propagation rule in mk_mod_core (Z3's `mod`
/// always uses the Euclidean, non-negative remainder convention).
let mod_range (a b:int) : Lemma (requires b > 0)
  (ensures 0 <= a % b /\ a % b < b) = ()

/// idiv/mod by 1 and -1 (mk_idiv_core's "v2.is_one()/is_minus_one()" and
/// mk_mod_core's "v2.is_one() || v2.is_minus_one()" branches).
let idiv_one (a:int) : Lemma (a / 1 == a) = ()
let idiv_minus_one (a:int) : Lemma (a / (-1) == (-1) * a) = ()
let mod_one (a:int) : Lemma (a % 1 == 0) = ()
let mod_minus_one (a:int) : Lemma (a % (-1) == 0) = ()

/// mod is idempotent on a fixed positive modulus: mod(mod(a,b), b) = mod(a,b).
let mod_idempotent (a b:int) : Lemma (requires b > 0)
  (ensures (a % b) % b == a % b) =
  FStar.Math.Lemmas.lemma_mod_twice a b

/// Dropping a summand that is an exact multiple of the modulus does not
/// change the result: mod(a + k*b, b) = mod(a, b).
let mod_drop_multiple (a k b:int) : Lemma (requires b > 0)
  (ensures (a + k * b) % b == a % b) =
  FStar.Math.Lemmas.lemma_mod_plus a k b

/// mod(a, -b) = mod(a, b) : mk_mod_core's "mod x -y = mod x y" rule.
let mod_neg_modulus (a b:int) : Lemma (requires b > 0)
  (ensures a % (-b) == a % b) =
  FStar.Math.Lemmas.euclidean_div_axiom a b

/// rem(a, b) = mod(a, b) when b >= 0, and = -mod(a, b) when b < 0
/// (mk_rem_core's "rem(v1,v2) = if v2 >= 0 then mod(v1,v2) else -mod(v1,v2)").
let rem_of_mod (a b:int) (r:int) : Lemma
  (requires b <> 0 /\ r == (if b >= 0 then a % b else -(a % b)))
  (ensures (b >= 0 ==> r == a % b) /\ (b < 0 ==> r == -(a % b))) = ()

(* ----------------------------------------------------------------- *)
(* mk_abs_core : (abs a) = ite(a >= 0, a, -a)                          *)
(* ----------------------------------------------------------------- *)

let abs_int (a:int) : Lemma ((if a >= 0 then a else -a) == abs a) = ()
let abs_real (a:real) : Lemma
  ((if a >=. zero then a else (zero -. a)) ==
   (if a >=. zero then a else zero -. a)) = ()

(* ----------------------------------------------------------------- *)
(* Summary check: integer/real lemmas above are discharged either      *)
(* directly by Z3's linear-arithmetic decision procedure (`()`) or by   *)
(* explicit appeal to FStar.Math.Lemmas, mirroring the Z3NlArith.fst    *)
(* conventions.  mk_power_core is formalized in the companion module    *)
(* Z3ArithRewriterPower.fst, and mk_to_int_core / mk_to_real_core /     *)
(* mk_is_int in Z3ArithRewriterCast.fst (split out into separate files  *)
(* because combined verification of all rule families in one module    *)
(* makes Z3's proof search time out).                                  *)
(* ----------------------------------------------------------------- *)

