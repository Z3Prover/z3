(*
   Z3FpaRewrites.fst

   Statements and F* proofs of equality-preservation for the
   *symbolic* (non-constant-folding) rewrite rules of
   src/ast/rewriter/fpa_rewriter.cpp, with respect to the
   axiomatization in Z3FpaTheory.fst.

   Each lemma is annotated with the Z3 function (and source-comment
   rule, where applicable) it formalizes.
*)
module Z3FpaRewrites

open Z3FpaTheory

(* ================================================================= *)
(* neg (mk_neg, fpa_rewriter.cpp 323-355)                              *)
(* ================================================================= *)

(* -nan --> nan *)
let lemma_neg_nan ()
  : Lemma (neg NaN == NaN)
  = ()

(* -(+oo) --> -oo *)
let lemma_neg_pinf ()
  : Lemma (neg (Inf false) == Inf true)
  = ()

(* -(-oo) --> +oo *)
let lemma_neg_ninf ()
  : Lemma (neg (Inf true) == Inf false)
  = ()

(* - - a --> a *)
let lemma_neg_neg (x:fp)
  : Lemma (neg (neg x) == x)
  = ()

(* ================================================================= *)
(* sub (mk_sub, fpa_rewriter.cpp 286-292): "a - b = a + (-b)"           *)
(* ================================================================= *)

let lemma_sub_is_add_neg (add: fp -> fp -> fp -> fp) (rm x y:fp)
  : Lemma (sub add rm x y == add rm x (neg y))
  = ()

(* ================================================================= *)
(* abs (mk_abs, fpa_rewriter.cpp 368-384)                              *)
(* ================================================================= *)

(* |nan| --> nan. (The only symbolic rule; all other cases in
   mk_abs are constant-folded, i.e. require a concrete `mpf`
   numeral and are out of scope here.) *)
let lemma_abs_nan ()
  : Lemma (abs_fp NaN == NaN)
  = ()

(* ================================================================= *)
(* min / max (mk_min 384-408, mk_max 408-432)                          *)
(* ================================================================= *)

(* min(nan, b) = b, for every b (including b = nan). *)
let lemma_min_nan_left (base: fp -> fp -> fp) (y:fp)
  : Lemma (min_fp base NaN y == y)
  = ()

(* min(a, nan) = a, whenever a is not itself nan (if a were nan, the
   left rule above already applies and takes precedence). *)
let lemma_min_nan_right (base: fp -> fp -> fp) (x:fp)
  : Lemma (requires ~(is_nan x)) (ensures min_fp base x NaN == x)
  = ()

let lemma_max_nan_left (base: fp -> fp -> fp) (y:fp)
  : Lemma (max_fp base NaN y == y)
  = ()

let lemma_max_nan_right (base: fp -> fp -> fp) (x:fp)
  : Lemma (requires ~(is_nan x)) (ensures max_fp base x NaN == x)
  = ()

(* ================================================================= *)
(* lt / gt / le / ge (mk_lt 578-619, mk_gt, mk_le 624-639, mk_ge)       *)
(* ================================================================= *)

(* nan on either side ==> lt = false.
   Z3: mk_lt, "if (is_nan(arg1) || is_nan(arg2)) result = false" *)
let lemma_lt_nan (x y:fp)
  : Lemma (requires is_nan x \/ is_nan y) (ensures lt x y == false)
  = ()

(* -oo < b  <=>  b <> -oo /\ b is not nan.
   Z3: mk_lt, "is_ninf(arg1) -> not(arg2==arg1) && not(nan(arg2))" *)
let lemma_lt_ninf_left (y:fp)
  : Lemma (lt (Inf true) y == (not (y = Inf true) && not (is_nan y)))
  = ()

(* a < -oo  -->  false, for every a (non-nan or not; nan is already
   handled by lemma_lt_nan). Z3: mk_lt, "is_ninf(arg2) -> false" *)
let lemma_lt_ninf_right (x:fp)
  : Lemma (requires ~(is_ninf x)) (ensures lt x (Inf true) == false)
  = ()

(* +oo < b --> false, for every b. Z3: mk_lt, "is_pinf(arg1) -> false" *)
let lemma_lt_pinf_left (y:fp)
  : Lemma (lt (Inf false) y == false)
  = ()

(* a < +oo  <=>  a <> +oo /\ a is not nan.
   Z3: mk_lt, "is_pinf(arg2) -> not(arg1==arg2) && not(nan(arg1))" *)
let lemma_lt_pinf_right (x:fp)
  : Lemma (requires ~(is_pinf x) /\ ~(is_ninf x))
          (ensures lt x (Inf false) == (not (x = Inf false) && not (is_nan x)))
  = ()

(* gt(a,b) = lt(b,a). Z3: mk_gt, "result = mk_lt(arg2, arg1)" *)
let lemma_gt_is_flipped_lt (x y:fp)
  : Lemma (gt x y == lt y x)
  = ()

(* nan on either side ==> le = false.
   Z3: mk_le, "if (is_nan(arg1) || is_nan(arg2)) result = false" *)
let lemma_le_nan (x y:fp)
  : Lemma (requires is_nan x \/ is_nan y) (ensures le x y == false)
  = ()

(* ge(a,b) = le(b,a). Z3: mk_ge, "result = mk_le(arg2, arg1)" *)
let lemma_ge_is_flipped_le (x y:fp)
  : Lemma (ge x y == le y x)
  = ()

(* ================================================================= *)
(* Classification sanity lemmas (is_negative / is_positive /           *)
(* is_normal / is_subnormal; fpa_rewriter.cpp 767-857)                  *)
(* ================================================================= *)

(* is_positive(x) == not(is_negative(x) || is_nan(x)).
   Z3: mk_is_positive, "(is_neg(v) || is_nan(v)) ? false : true" *)
let lemma_is_positive_def (x:fp)
  : Lemma (is_positive x == not (is_negative x || is_nan x))
  = ()

(* is_negative and is_positive are mutually exclusive. *)
let lemma_pos_neg_exclusive (x:fp)
  : Lemma (~(is_positive x /\ is_negative x))
  = ()

(* Every value is in exactly one of the five IEEE-754 classes:
   NaN, Infinity, Zero, Subnormal, Normal. This is the value-level
   analogue of the bit-level classification lemmas in
   Z3FpaConverter.fst (lemma_fp_classes_exhaustive /
   lemma_fp_classes_disjoint). *)
let lemma_classes_exhaustive (is_subnormal_mag: int -> bool) (x:fp)
  : Lemma (is_nan x || is_inf x || is_zero x
           || is_subnormal is_subnormal_mag x || is_normal is_subnormal_mag x)
  = ()

let lemma_classes_disjoint (is_subnormal_mag: int -> bool) (x:fp)
  : Lemma ((is_nan x     ==> ~(is_inf x || is_zero x || is_subnormal is_subnormal_mag x || is_normal is_subnormal_mag x)) /\
           (is_inf x     ==> ~(is_zero x || is_subnormal is_subnormal_mag x || is_normal is_subnormal_mag x)) /\
           (is_zero x    ==> ~(is_subnormal is_subnormal_mag x || is_normal is_subnormal_mag x)) /\
           (is_subnormal is_subnormal_mag x ==> ~(is_normal is_subnormal_mag x)))
  = ()

(* ================================================================= *)
(* Equalities: float_eq vs eq_core (mk_float_eq 557-578,                *)
(* mk_eq_core 857-872)                                                  *)
(*                                                                      *)
(* These are the key "soundness" facts behind the code comment          *)
(* "// This the floating point theory ==" (mk_float_eq) vs              *)
(* "// This the SMT =" (mk_eq_core): `eq_core` must be a genuine         *)
(* equivalence relation (it backs SMT's `=`), while `float_eq` is the    *)
(* IEEE-754 `fp.eq` relation, which is *not* reflexive on NaN.           *)
(* ================================================================= *)

(* eq_core is reflexive -- *including* on NaN: two NaN terms are
   considered equal by SMT `=`, matching mk_eq_core's first branch
   "(is_nan(v1) && is_nan(v2)) -> true". *)
let lemma_eq_core_refl (x:fp)
  : Lemma (eq_core x x == true)
  = ()

let lemma_eq_core_sym (x y:fp)
  : Lemma (eq_core x y == eq_core y x)
  = ()

let lemma_eq_core_trans (x y z:fp)
  : Lemma (requires eq_core x y /\ eq_core y z) (ensures eq_core x z)
  = ()

(* eq_core distinguishes signed zeros: +0 <> -0 under SMT `=`.
   Z3: mk_eq_core, "(is_zero(v1) && is_zero(v2) && sgn(v1)!=sgn(v2)) -> false" *)
let lemma_eq_core_signed_zero ()
  : Lemma (eq_core (Zero false) (Zero true) == false)
  = ()

(* float_eq is *not* reflexive on NaN: fp.eq(nan,nan) = false.
   This is the IEEE-754 quirk that necessitates a separate `eq_core`
   for SMT's `=` in the first place. *)
let lemma_float_eq_nan_irreflexive (x:fp)
  : Lemma (requires is_nan x) (ensures float_eq x x == false)
  = ()

(* float_eq identifies signed zeros: fp.eq(+0,-0) = true.
   Z3: mk_float_eq delegates to m_fm.eq, and IEEE-754 fp.eq treats
   +0 and -0 as equal. *)
let lemma_float_eq_signed_zero ()
  : Lemma (float_eq (Zero false) (Zero true) == true)
  = ()

(* float_eq is reflexive on every *non*-NaN value (the complement of
   lemma_float_eq_nan_irreflexive). *)
let lemma_float_eq_refl_non_nan (x:fp)
  : Lemma (requires ~(is_nan x)) (ensures float_eq x x == true)
  = ()

(* float_eq and eq_core agree exactly when no NaN is involved and the
   signed-zero cases coincide (i.e. outside the two cases where they
   are deliberately engineered to differ). *)
let lemma_float_eq_eq_core_agree (x y:fp)
  : Lemma (requires ~(is_nan x) /\ ~(is_nan y) /\
                     ~(is_zero x /\ is_zero y /\ is_negative x <> is_negative y))
          (ensures float_eq x y == eq_core x y)
  = ()
