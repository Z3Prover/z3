(*
  FPARewriterRules.fst

  Formalization of the floating-point rewrite rules introduced in
  Z3 PR #9038 ("fix #8185: add FPA rewriter simplifications for fma
  with zero multiplicand and classification of int-to-float conversions").

  The PR adds three families of optimizations to fpa_rewriter.cpp:

    1. fma(rm, ±0, y, z): zero-multiplicand decomposition.
       Instead of bit-blasting the full FMA circuit, decompose into
       a cheaper fp_add when one multiplicand is a concrete zero.

    2. isNaN/isInf/isNormal applied to to_fp(rm, to_real(int_expr)):
       replace with pure integer/arithmetic constraints.

    3. Push isNaN/isInf/isNormal through ite when both branches are
       concrete FP numerals.

  Each lemma below states and proves (from the axioms in IEEE754.fst)
  the mathematical content of the corresponding C++ simplification.
  The preconditions mirror the guards checked by the C++ rewriter before
  applying each rewrite.

  Naming convention:
    lemma_fma_*        — Section 1, FMA with zero multiplicand
    lemma_is_nan_*     — Section 2a, isNaN of integer-to-float
    lemma_is_inf_*     — Section 2b, isInf  of integer-to-float
    lemma_is_normal_*  — Section 2c, isNormal of integer-to-float
    lemma_*_ite        — Section 3, classification through ite
*)

module FPARewriterRules

open IEEE754

(* ================================================================== *)
(* Section 1: FMA with a Zero Multiplicand                            *)
(*                                                                     *)
(* C++ location: fpa_rewriter.cpp, mk_fma, new block after line 428   *)
(*                                                                     *)
(* When arg2 (or arg3) is a concrete ±0, the rewriter avoids          *)
(* building the full FMA bit-blast circuit.  The simplifications       *)
(* below correspond to each branch in the C++ code.                   *)
(*                                                                     *)
(* We formalize fma(rm, ±0, y, z); the symmetric case                 *)
(* fma(rm, x, ±0, z) follows by the same argument with x and y        *)
(* swapped (fp_mul is commutative for sign and NaN-propagation         *)
(* purposes; a separate symmetric set of axioms could be added).      *)
(* ================================================================== *)

(* 1a.  fma(rm, ±0, y, NaN) = NaN
        Source: C++ fpa_rewriter.cpp, mk_fma, branch "if (m_util.is_nan(arg4))".
        The addend NaN propagates (IEEE 754-2019 §6.2, NaN payload rules).
        [extract: FPA_REWRITE_FMA_ZERO_MUL, case (a)] *)
let lemma_fma_zero_nan_addend
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y: float eb sb)
    : Lemma (requires is_zero zero_val = true)
            (ensures  is_nan (fp_fma rm zero_val y (nan #eb #sb)) = true) =
  ax_fma_nan_z rm zero_val y


(* 1b.  fma(rm, ±0, NaN, z) = NaN
        Source: C++ check "m_fm.is_nan(vo)" for other_mul.
        NaN in the second multiplicand propagates regardless of the addend.
        [extract: FPA_REWRITE_FMA_ZERO_MUL, case (b)] *)
let lemma_fma_zero_nan_mul
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val z: float eb sb)
    : Lemma (requires is_zero zero_val = true)
            (ensures  is_nan (fp_fma rm zero_val (nan #eb #sb) z) = true) =
  ax_fma_nan_y rm zero_val z


(* 1c.  fma(rm, ±0, ±∞, z) = NaN
        Source: C++ check "m_fm.is_inf(vo)" for other_mul.
        0 * ∞ is the "invalid operation" NaN (IEEE 754-2019 §7.2),
        which then propagates through the addition.
        [extract: FPA_REWRITE_FMA_ZERO_MUL, case (b)] *)
let lemma_fma_zero_inf_mul
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val inf_val z: float eb sb)
    : Lemma (requires is_zero zero_val = true && is_inf inf_val = true)
            (ensures  is_nan (fp_fma rm zero_val inf_val z) = true) =
  ax_zero_mul_inf rm zero_val inf_val;
  ax_fma_nan_mul  rm zero_val inf_val z


(* 1d.  fma(rm, ±0, y_finite, z) = fp_add(rm, fp_mul(rm, ±0, y_finite), z)
        Source: C++ branch "m_util.is_numeral(other_mul, vo)" (concrete finite).
        ±0 * finite = ±0 exactly (IEEE 754-2019 §6.3), so fma reduces to
        an addition whose first operand is the computed ±0 product.

        This is the key decomposition that replaces the expensive FMA
        circuit with a cheaper addition.
        [extract: FPA_REWRITE_FMA_ZERO_MUL, case (c)] *)
let lemma_fma_zero_finite_decomposes
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y z: float eb sb)
    : Lemma (requires is_zero zero_val = true && is_finite y = true)
            (ensures  fp_fma rm zero_val y z =
                      fp_add rm (fp_mul rm zero_val y) z &&
                      is_zero (fp_mul rm zero_val y) = true) =
  ax_fma_zero_finite rm zero_val y z


(* 1e.  fma(rm, ±0, y_finite, z_nonzero_finite) = z_nonzero_finite
        Source: C++ branch with "m_util.is_numeral(arg4, vz) && !m_fm.is_zero(vz)"
        and a concrete finite other_mul.
        When z is nonzero and finite, ±0 + z = z exactly under any rounding
        mode (IEEE 754-2019 §6.3), so the entire fma collapses to z.
        [extract: FPA_REWRITE_FMA_ZERO_MUL, case (c) folded with ax_add_zero_nonzero] *)
let lemma_fma_zero_const_addend
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y z: float eb sb)
    : Lemma (requires is_zero zero_val = true &&
                      is_finite y      = true &&
                      is_finite z      = true &&
                      is_zero z        = false)
            (ensures  fp_fma rm zero_val y z = z) =
  ax_fma_zero_finite  rm zero_val y z;
  ax_add_zero_nonzero rm (fp_mul rm zero_val y) z


(* 1f.  Symbolic y, concrete nonzero non-NaN z:
          fma(rm, ±0, y, z_const) =
            ite(¬isNaN(y) ∧ ¬isInf(y),   z_const,   NaN)
        Source: C++ branch producing "m().mk_ite(finite_cond, arg4, nan)".
        We prove each arm of the ite separately.
        [extract: FPA_REWRITE_FMA_ZERO_MUL, case (d)]

        Finite arm: y is finite → fma = z_const (by 1e). *)
let lemma_fma_zero_const_finite_arm
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y z: float eb sb)
    : Lemma (requires is_zero zero_val = true &&
                      is_finite y      = true &&
                      is_finite z      = true &&
                      is_zero z        = false)
            (ensures  fp_fma rm zero_val y z = z) =
  lemma_fma_zero_const_addend rm zero_val y z

(* NaN-or-inf arm: y is NaN or ∞ → fma = NaN. *)
let lemma_fma_zero_const_nan_inf_arm
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y z: float eb sb)
    : Lemma (requires is_zero zero_val = true &&
                      (is_nan y = true || is_inf y = true))
            (ensures  is_nan (fp_fma rm zero_val y z) = true) =
  if is_nan y = true then
    ax_fma_any_nan_y rm zero_val y z
  else begin
    ax_zero_mul_inf rm zero_val y;
    ax_fma_nan_mul  rm zero_val y z
  end


(* 1g.  General case — symbolic y and z:
          fma(rm, ±0, y, z) =
            ite(is_finite(y),  fp_add(rm, product_zero, z),  NaN)
        Source: C++ block producing the final ite with product_zero.
        product_zero is ±0 with sign = sign(±0) XOR sign(y).
        We prove each arm.
        [extract: FPA_REWRITE_FMA_ZERO_MUL, case (e)] *)

(* Finite arm: fma = fp_add(rm, fp_mul(rm, ±0, y), z). *)
let lemma_fma_zero_general_finite_arm
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y z: float eb sb)
    : Lemma (requires is_zero zero_val = true && is_finite y = true)
            (ensures  fp_fma rm zero_val y z =
                      fp_add rm (fp_mul rm zero_val y) z &&
                      is_zero (fp_mul rm zero_val y) = true) =
  ax_fma_zero_finite rm zero_val y z

(* NaN-or-inf arm: fma = NaN. *)
let lemma_fma_zero_general_nan_inf_arm
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y z: float eb sb)
    : Lemma (requires is_zero zero_val = true &&
                      (is_nan y = true || is_inf y = true))
            (ensures  is_nan (fp_fma rm zero_val y z) = true) =
  if is_nan y = true then
    ax_fma_any_nan_y rm zero_val y z
  else begin
    ax_zero_mul_inf rm zero_val y;
    ax_fma_nan_mul  rm zero_val y z
  end

(* Sign of the zero product (IEEE 754-2019 §6.3):
   sign(fp_mul(rm, ±0, y)) = sign(±0) XOR sign(y) for finite nonzero y. *)
let lemma_fma_zero_product_sign
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y: float eb sb)
    : Lemma (requires is_zero zero_val = true &&
                      is_finite y      = true &&
                      is_zero y        = false)
            (ensures  (let p = fp_mul rm zero_val y in
                       is_zero p = true &&
                       (is_negative p =
                         ((is_negative zero_val && not (is_negative y)) ||
                          (not (is_negative zero_val) && is_negative y))))) =
  ax_zero_mul_sign rm zero_val y


(* ================================================================== *)
(* Section 2: Classification of Integer-to-Float Conversions          *)
(*                                                                     *)
(* C++ location: fpa_rewriter.cpp, mk_is_nan / mk_is_inf /            *)
(*               mk_is_normal, new blocks added by PR #9038.           *)
(*                                                                     *)
(* The rewriter detects the pattern isX(to_fp(rm, to_real(int_expr))) *)
(* and replaces it with a pure integer arithmetic constraint.          *)
(*                                                                     *)
(* Key invariants for to_fp_of_int (proved from axioms in IEEE754.fst):*)
(*   - Never NaN      (ax_to_fp_int_not_nan)                          *)
(*   - Never subnormal (ax_to_fp_int_not_subnormal)                   *)
(*   - Zero iff x = 0  (ax_to_fp_int_zero, ax_to_fp_int_nonzero)     *)
(*   - Inf iff x exceeds the format's overflow threshold               *)
(* ================================================================== *)

(* --- 2a: isNaN --- *)

(* isNaN(to_fp(rm, x)) = false for any integer x.
   Source: C++ block in mk_is_nan checking "a->get_num_args() == 2 &&
   (m_util.au().is_real(a->get_arg(1)) || m_util.au().is_int(a->get_arg(1)))".
   [extract: FPA_REWRITE_IS_NAN_TO_FP_INT] *)
let lemma_is_nan_to_fp_int
    (#eb #sb: pos) (rm: rounding_mode) (x: int)
    : Lemma (is_nan (to_fp_of_int #eb #sb rm x) = false) =
  ax_to_fp_int_not_nan #eb #sb rm x


(* --- 2b: isInf --- *)

(* Source: C++ function mk_is_inf_of_int, called from mk_is_inf.
   Each lemma corresponds to one case in the switch(rm) statement.
   [extract: FPA_REWRITE_IS_INF_TO_FP_INT, helper mk_is_inf_of_int] *)

(* RNE: overflow iff |x| >= overflow_threshold(eb, sb).
   At the boundary the significand of MAX_FINITE is odd, so RNE rounds
   to even, which means rounding to ∞. *)
let lemma_is_inf_to_fp_int_rne
    (#eb #sb: pos) (x: int)
    : Lemma (is_inf (to_fp_of_int #eb #sb RNE x) =
             (x >= overflow_threshold eb sb || x <= -(overflow_threshold eb sb))) =
  ax_is_inf_rne #eb #sb x

(* RNA: same threshold as RNE (ties round away from zero to ∞). *)
let lemma_is_inf_to_fp_int_rna
    (#eb #sb: pos) (x: int)
    : Lemma (is_inf (to_fp_of_int #eb #sb RNA x) =
             (x >= overflow_threshold eb sb || x <= -(overflow_threshold eb sb))) =
  ax_is_inf_rna #eb #sb x

(* RTP: positive overflow only (negative values round toward 0, not -∞). *)
let lemma_is_inf_to_fp_int_rtp
    (#eb #sb: pos) (x: int)
    : Lemma (is_inf (to_fp_of_int #eb #sb RTP x) = (x > max_finite_int eb sb)) =
  ax_is_inf_rtp #eb #sb x

(* RTN: negative overflow only (positive values round toward 0, not +∞). *)
let lemma_is_inf_to_fp_int_rtn
    (#eb #sb: pos) (x: int)
    : Lemma (is_inf (to_fp_of_int #eb #sb RTN x) = (x < -(max_finite_int eb sb))) =
  ax_is_inf_rtn #eb #sb x

(* RTZ: truncation toward zero never overflows to infinity. *)
let lemma_is_inf_to_fp_int_rtz
    (#eb #sb: pos) (x: int)
    : Lemma (is_inf (to_fp_of_int #eb #sb RTZ x) = false) =
  ax_is_inf_rtz #eb #sb x


(* --- 2c: isNormal --- *)

(* isNormal(to_fp(rm, x)) ↔ x ≠ 0 ∧ ¬isInf(to_fp(rm, x))
   Source: C++ block in mk_is_normal:
     "expr_ref not_zero(...); expr_ref inf_cond = mk_is_inf_of_int(...);
      result = m().mk_and(not_zero, m().mk_not(inf_cond));"
   [extract: FPA_REWRITE_IS_NORMAL_TO_FP_INT]

   Proof sketch:
     For integer x, to_fp is never NaN (by ax_to_fp_int_not_nan) and
     never subnormal (by ax_to_fp_int_not_subnormal).  By the exhaustive
     classification axiom (ax_classification), the result must be one of:
       zero, normal, or infinite.
     Therefore:
       - if x = 0: result is zero, hence NOT normal.
       - if x ≠ 0: result is not zero (by ax_to_fp_int_nonzero), so
           result is normal iff it is not infinite. *)
let lemma_is_normal_to_fp_int
    (#eb #sb: pos) (rm: rounding_mode) (x: int)
    : Lemma (is_normal (to_fp_of_int #eb #sb rm x) =
             (x <> 0 && not (is_inf (to_fp_of_int #eb #sb rm x)))) =
  let f = to_fp_of_int #eb #sb rm x in
  ax_to_fp_int_not_nan       #eb #sb rm x;   (* is_nan f = false      *)
  ax_to_fp_int_not_subnormal #eb #sb rm x;   (* is_subnormal f = false *)
  ax_classification          f;              (* nan||inf||zero||normal||subnormal *)
  if x = 0 then begin
    ax_to_fp_int_zero #eb #sb rm;            (* is_zero f = true  *)
    ax_zero_exclusive f                      (* is_normal f = false, since is_zero f *)
  end else begin
    ax_to_fp_int_nonzero #eb #sb rm x;       (* is_zero f = false *)
    (* At this point: not nan, not subnormal, not zero.
       ax_classification gives nan||inf||zero||normal||subnormal, which
       simplifies to inf||normal.  We case-split on is_inf f. *)
    if is_inf f then
      ax_inf_exclusive f                     (* is_inf f = true => is_normal f = false *)
    else
      ()                                     (* is_inf f = false; by classification, is_normal f = true *)
  end


(* ================================================================== *)
(* Section 3: Classification Predicates Pushed through ite            *)
(*                                                                     *)
(* C++ location: fpa_rewriter.cpp, mk_is_nan / mk_is_inf /            *)
(*               mk_is_normal, new blocks "Push through ite when both *)
(*               branches are concrete FP numerals."                  *)
(*                                                                     *)
(* In the C++ rewriter the rule is applied only when both branches    *)
(* are concrete numerals, so the classification can be evaluated at   *)
(* rewrite time.  Mathematically the identity holds unconditionally   *)
(* because is_nan, is_inf, and is_normal are total boolean functions. *)
(*                                                                     *)
(* These lemmas are trivial in F*: applying a function to             *)
(* (if c then t else e) reduces by computation to                     *)
(* (if c then f(t) else f(e)) for any total f.                        *)
(* ================================================================== *)

(* 3a.  isNaN(ite(c, t, e)) = ite(c, isNaN(t), isNaN(e))
        Source: C++ block producing "m().mk_ite(c, is_nan(t) ? true : false,
                                                   is_nan(e) ? true : false)".
        [extract: FPA_REWRITE_IS_NAN_ITE] *)
let lemma_is_nan_ite
    (#eb #sb: pos) (c: bool) (t e: float eb sb)
    : Lemma (is_nan (if c then t else e) =
             (if c then is_nan t else is_nan e)) = ()


(* 3b.  isInf(ite(c, t, e)) = ite(c, isInf(t), isInf(e))
        Source: same pattern in mk_is_inf.
        [extract: FPA_REWRITE_IS_INF_ITE] *)
let lemma_is_inf_ite
    (#eb #sb: pos) (c: bool) (t e: float eb sb)
    : Lemma (is_inf (if c then t else e) =
             (if c then is_inf t else is_inf e)) = ()


(* 3c.  isNormal(ite(c, t, e)) = ite(c, isNormal(t), isNormal(e))
        Source: same pattern in mk_is_normal.
        [extract: FPA_REWRITE_IS_NORMAL_ITE] *)
let lemma_is_normal_ite
    (#eb #sb: pos) (c: bool) (t e: float eb sb)
    : Lemma (is_normal (if c then t else e) =
             (if c then is_normal t else is_normal e)) = ()


(* ================================================================== *)
(* Section 4: Composite correctness statements                        *)
(*                                                                     *)
(* These lemmas combine the individual results from Sections 1-3      *)
(* to state the overall correctness of each rewrite as the C++        *)
(* code produces it.                                                  *)
(* ================================================================== *)

(* The full FMA zero-multiplicand rewrite.
   When zero_val is ±0 and y is symbolic, the rewriter produces:
     ite(is_finite(y), fp_add(rm, fp_mul(rm, ±0, y), z), NaN)
   We state this as two implications, one per arm of the ite.

   Note: we use is_nan rather than equality with the canonical nan
   constant because IEEE 754 does not prescribe a unique NaN encoding;
   Z3 uses a canonical NaN internally, but that is an implementation
   choice beyond the scope of this formalization. *)
let lemma_fma_zero_ite_finite_arm
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y z: float eb sb)
    : Lemma (requires is_zero zero_val = true && is_finite y = true)
            (ensures  fp_fma rm zero_val y z =
                      fp_add rm (fp_mul rm zero_val y) z &&
                      is_zero (fp_mul rm zero_val y) = true) =
  ax_fma_zero_finite rm zero_val y z

let lemma_fma_zero_ite_nan_arm
    (#eb #sb: pos)
    (rm: rounding_mode) (zero_val y z: float eb sb)
    : Lemma (requires is_zero zero_val = true && is_finite y = false)
            (ensures  is_nan (fp_fma rm zero_val y z) = true) =
  if is_nan y = true then
    ax_fma_any_nan_y rm zero_val y z
  else begin
    (* is_finite y = false && is_nan y = false.
       By the transparent definition is_finite y = not (is_nan y) && not (is_inf y),
       the type-checker can derive is_inf y = true directly. *)
    assert (is_inf y = true);
    ax_zero_mul_inf rm zero_val y;
    ax_fma_nan_mul  rm zero_val y z
  end


(* The full isNormal(to_fp(rm, x)) rewrite for RNE/RNA (most common mode).
   Combining Sections 2b and 2c for RNE. *)
let lemma_is_normal_to_fp_int_rne
    (#eb #sb: pos) (x: int)
    : Lemma (is_normal (to_fp_of_int #eb #sb RNE x) =
             (x <> 0 &&
              not (x >= overflow_threshold eb sb ||
                   x <= -(overflow_threshold eb sb)))) =
  lemma_is_normal_to_fp_int #eb #sb RNE x;
  ax_is_inf_rne #eb #sb x

(* The full isNormal(to_fp(rm, x)) rewrite for RTZ (never overflows). *)
let lemma_is_normal_to_fp_int_rtz
    (#eb #sb: pos) (x: int)
    : Lemma (is_normal (to_fp_of_int #eb #sb RTZ x) = (x <> 0)) =
  lemma_is_normal_to_fp_int #eb #sb RTZ x;
  ax_is_inf_rtz #eb #sb x
