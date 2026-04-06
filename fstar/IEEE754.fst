(*
  IEEE754.fst

  Axiomatic theory of IEEE 754 floating-point arithmetic for use with
  Z3's fpa_rewriter formalization.

  All declarations prefixed with "ax_" are assumed axioms — consequences
  of the IEEE 754-2019 standard that we take as given rather than
  deriving from a bit-level representation.

  The float type is parameterized by
    eb : pos  -- number of exponent bits
    sb : pos  -- number of significand bits (including the implicit leading bit)

  This matches the parameterization used throughout Z3's fpa_decl_plugin
  and mpf_manager.
*)

module IEEE754

(* ------------------------------------------------------------------ *)
(* Floating-point type                                                  *)
(* ------------------------------------------------------------------ *)

(* Abstract IEEE 754 float parameterized by format.  A concrete model
   would be a triple (sign, biased_exponent, significand), but we keep
   the type opaque so the axioms are the only assumed properties. *)
assume val float : (eb: pos) -> (sb: pos) -> eqtype

(* ------------------------------------------------------------------ *)
(* Rounding modes (IEEE 754-2019 §4.3)                                 *)
(* ------------------------------------------------------------------ *)

type rounding_mode =
  | RNE   (* roundTiesToEven     *)
  | RNA   (* roundTiesToAway     *)
  | RTP   (* roundTowardPositive *)
  | RTN   (* roundTowardNegative *)
  | RTZ   (* roundTowardZero     *)

(* ------------------------------------------------------------------ *)
(* Classification predicates (IEEE 754-2019 §5.7.2)                   *)
(* ------------------------------------------------------------------ *)

assume val is_nan      : #eb:pos -> #sb:pos -> float eb sb -> bool
assume val is_inf      : #eb:pos -> #sb:pos -> float eb sb -> bool
assume val is_zero     : #eb:pos -> #sb:pos -> float eb sb -> bool
assume val is_normal   : #eb:pos -> #sb:pos -> float eb sb -> bool
assume val is_subnormal: #eb:pos -> #sb:pos -> float eb sb -> bool
assume val is_negative : #eb:pos -> #sb:pos -> float eb sb -> bool
assume val is_positive : #eb:pos -> #sb:pos -> float eb sb -> bool

(* Derived: finite = not NaN and not infinite.
   This matches Z3's is_finite check in fpa_rewriter.cpp. *)
let is_finite (#eb #sb: pos) (x: float eb sb) : bool =
  not (is_nan x) && not (is_inf x)

(* ------------------------------------------------------------------ *)
(* Classification axioms                                                *)
(* ------------------------------------------------------------------ *)

(* Every float belongs to exactly one of the five IEEE 754 classes. *)
assume val ax_classification :
  #eb:pos -> #sb:pos -> (x: float eb sb) ->
  Lemma (is_nan x || is_inf x || is_zero x || is_normal x || is_subnormal x)

(* The five classes are mutually exclusive. *)
assume val ax_nan_exclusive :
  #eb:pos -> #sb:pos -> (x: float eb sb) ->
  Lemma (requires is_nan x = true)
        (ensures  is_inf x = false && is_zero x = false &&
                  is_normal x = false && is_subnormal x = false)

assume val ax_inf_exclusive :
  #eb:pos -> #sb:pos -> (x: float eb sb) ->
  Lemma (requires is_inf x = true)
        (ensures  is_nan x = false && is_zero x = false &&
                  is_normal x = false && is_subnormal x = false)

assume val ax_zero_exclusive :
  #eb:pos -> #sb:pos -> (x: float eb sb) ->
  Lemma (requires is_zero x = true)
        (ensures  is_nan x = false && is_inf x = false &&
                  is_normal x = false && is_subnormal x = false)

assume val ax_normal_exclusive :
  #eb:pos -> #sb:pos -> (x: float eb sb) ->
  Lemma (requires is_normal x = true)
        (ensures  is_nan x = false && is_inf x = false &&
                  is_zero x = false && is_subnormal x = false)

assume val ax_subnormal_exclusive :
  #eb:pos -> #sb:pos -> (x: float eb sb) ->
  Lemma (requires is_subnormal x = true)
        (ensures  is_nan x = false && is_inf x = false &&
                  is_zero x = false && is_normal x = false)

(* Zeros are finite (not NaN, not inf). *)
let lemma_zero_is_finite
    (#eb #sb: pos) (x: float eb sb)
    : Lemma (requires is_zero x = true) (ensures is_finite x = true) =
  ax_zero_exclusive x

(* ------------------------------------------------------------------ *)
(* Named constants                                                      *)
(* ------------------------------------------------------------------ *)

assume val nan   : #eb:pos -> #sb:pos -> float eb sb
assume val pinf  : #eb:pos -> #sb:pos -> float eb sb
assume val ninf  : #eb:pos -> #sb:pos -> float eb sb
assume val pzero : #eb:pos -> #sb:pos -> float eb sb
assume val nzero : #eb:pos -> #sb:pos -> float eb sb

assume val ax_nan_is_nan    : #eb:pos -> #sb:pos -> Lemma (is_nan  (nan   #eb #sb) = true)
assume val ax_pinf_is_inf   : #eb:pos -> #sb:pos -> Lemma (is_inf  (pinf  #eb #sb) = true)
assume val ax_ninf_is_inf   : #eb:pos -> #sb:pos -> Lemma (is_inf  (ninf  #eb #sb) = true)
assume val ax_pzero_is_zero : #eb:pos -> #sb:pos ->
  Lemma (is_zero (pzero #eb #sb) = true && is_positive (pzero #eb #sb) = true)
assume val ax_nzero_is_zero : #eb:pos -> #sb:pos ->
  Lemma (is_zero (nzero #eb #sb) = true && is_negative (nzero #eb #sb) = true)

(* ------------------------------------------------------------------ *)
(* Arithmetic operations                                                *)
(* ------------------------------------------------------------------ *)

assume val fp_add : #eb:pos -> #sb:pos ->
  rounding_mode -> float eb sb -> float eb sb -> float eb sb

assume val fp_mul : #eb:pos -> #sb:pos ->
  rounding_mode -> float eb sb -> float eb sb -> float eb sb

(* fp_fma rm x y z = roundToNearest(x * y + z), per IEEE 754-2019 §5.4 *)
assume val fp_fma : #eb:pos -> #sb:pos ->
  rounding_mode -> float eb sb -> float eb sb -> float eb sb -> float eb sb

(* ------------------------------------------------------------------ *)
(* NaN propagation axioms (IEEE 754-2019 §6.2)                        *)
(* ------------------------------------------------------------------ *)

assume val ax_add_nan_l :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (y: float eb sb) ->
  Lemma (is_nan (fp_add rm (nan #eb #sb) y) = true)

assume val ax_add_nan_r :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: float eb sb) ->
  Lemma (is_nan (fp_add rm x (nan #eb #sb)) = true)

assume val ax_mul_nan_l :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (y: float eb sb) ->
  Lemma (is_nan (fp_mul rm (nan #eb #sb) y) = true)

assume val ax_mul_nan_r :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: float eb sb) ->
  Lemma (is_nan (fp_mul rm x (nan #eb #sb)) = true)

assume val ax_fma_nan_x :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (y: float eb sb) -> (z: float eb sb) ->
  Lemma (is_nan (fp_fma rm (nan #eb #sb) y z) = true)

assume val ax_fma_nan_y :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: float eb sb) -> (z: float eb sb) ->
  Lemma (is_nan (fp_fma rm x (nan #eb #sb) z) = true)

assume val ax_fma_nan_z :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: float eb sb) -> (y: float eb sb) ->
  Lemma (is_nan (fp_fma rm x y (nan #eb #sb)) = true)

(* General NaN propagation: if any argument is NaN, the result is NaN. *)
assume val ax_fma_any_nan_x :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: float eb sb) -> (y: float eb sb) -> (z: float eb sb) ->
  Lemma (requires is_nan x = true)
        (ensures  is_nan (fp_fma rm x y z) = true)

assume val ax_fma_any_nan_y :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: float eb sb) -> (y: float eb sb) -> (z: float eb sb) ->
  Lemma (requires is_nan y = true)
        (ensures  is_nan (fp_fma rm x y z) = true)

assume val ax_fma_any_nan_z :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: float eb sb) -> (y: float eb sb) -> (z: float eb sb) ->
  Lemma (requires is_nan z = true)
        (ensures  is_nan (fp_fma rm x y z) = true)

(* ------------------------------------------------------------------ *)
(* Special-value arithmetic axioms                                      *)
(* ------------------------------------------------------------------ *)

(* 0 * ±∞ = NaN: "invalid operation" per IEEE 754-2019 §7.2. *)
assume val ax_zero_mul_inf :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) ->
  (zero_val: float eb sb) -> (inf_val: float eb sb) ->
  Lemma (requires is_zero zero_val = true && is_inf inf_val = true)
        (ensures  is_nan (fp_mul rm zero_val inf_val) = true &&
                  is_nan (fp_mul rm inf_val zero_val) = true)

(* If the product in fma is NaN, the whole fma is NaN.
   This covers the case where fp_mul rm x y = NaN and we need
   is_nan (fp_fma rm x y z) = true. *)
assume val ax_fma_nan_mul :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: float eb sb) -> (y: float eb sb) -> (z: float eb sb) ->
  Lemma (requires is_nan (fp_mul rm x y) = true)
        (ensures  is_nan (fp_fma rm x y z) = true)

(* fma(rm, zero, y_finite, z) = fp_add(rm, fp_mul(rm, zero, y_finite), z)
   and fp_mul(rm, zero, y_finite) is ±0 (exact, IEEE 754-2019 §6.3).
   This is the core decomposition used by the rewriter. *)
assume val ax_fma_zero_finite :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (zero_val: float eb sb) -> (y: float eb sb) -> (z: float eb sb) ->
  Lemma (requires is_zero zero_val = true && is_finite y = true)
        (ensures  fp_fma rm zero_val y z = fp_add rm (fp_mul rm zero_val y) z &&
                  is_zero (fp_mul rm zero_val y) = true)

(* Sign of 0 * y (IEEE 754-2019 §6.3):
   sign(0 * y) = sign(0) XOR sign(y) for finite nonzero y. *)
assume val ax_zero_mul_sign :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (zero_val: float eb sb) -> (y: float eb sb) ->
  Lemma (requires is_zero zero_val = true && is_finite y = true && is_zero y = false)
        (ensures  (let p = fp_mul rm zero_val y in
                   is_zero p = true &&
                   (is_negative p =
                     ((is_negative zero_val && not (is_negative y)) ||
                      (not (is_negative zero_val) && is_negative y)))))

(* fp_add(rm, ±0, z) = z when z is finite and nonzero (IEEE 754-2019 §6.3).
   ±0 is an additive identity for nonzero finite values under all rounding modes. *)
assume val ax_add_zero_nonzero :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (zero_val: float eb sb) -> (z: float eb sb) ->
  Lemma (requires is_zero zero_val = true && is_finite z = true && is_zero z = false)
        (ensures  fp_add rm zero_val z = z)

(* ------------------------------------------------------------------ *)
(* Integer-to-float conversion                                          *)
(* ------------------------------------------------------------------ *)

(* to_fp_of_int rm x: convert integer x to the nearest representable
   float in the (eb, sb) format, using rounding mode rm.
   This corresponds to to_fp(rm, to_real(x)) in Z3's SMT theory. *)
assume val to_fp_of_int : #eb:pos -> #sb:pos -> rounding_mode -> int -> float eb sb

(* Conversion of any integer never produces NaN (IEEE 754-2019 §5.4.1):
   NaN only arises from invalid operations, not from converting finite values. *)
assume val ax_to_fp_int_not_nan :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: int) ->
  Lemma (is_nan (to_fp_of_int #eb #sb rm x) = false)

(* Conversion of any integer never produces a subnormal value.
   Justification: the smallest nonzero integer has magnitude 1, and
   1.0 is a normal number in every IEEE 754 format (its biased exponent
   equals the bias, which is always in range). *)
assume val ax_to_fp_int_not_subnormal :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: int) ->
  Lemma (is_subnormal (to_fp_of_int #eb #sb rm x) = false)

(* 0 maps to a zero (the sign may depend on the rounding mode for RTN). *)
assume val ax_to_fp_int_zero :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) ->
  Lemma (is_zero (to_fp_of_int #eb #sb rm 0) = true)

(* A nonzero integer maps to a nonzero float. *)
assume val ax_to_fp_int_nonzero :
  #eb:pos -> #sb:pos -> (rm: rounding_mode) -> (x: int) ->
  Lemma (requires x <> 0)
        (ensures is_zero (to_fp_of_int #eb #sb rm x) = false)

(* ------------------------------------------------------------------ *)
(* Overflow thresholds for isInf(to_fp_of_int rm x)                   *)
(*                                                                     *)
(* overflow_threshold eb sb: the smallest integer magnitude that       *)
(* causes overflow to ±∞ under RNE and RNA.                           *)
(*   = ⌈MAX_FINITE + ULP(MAX_FINITE)/2⌉                               *)
(* where MAX_FINITE = (2 - 2^(1-sb)) * 2^(2^(eb-1)-1).               *)
(*                                                                     *)
(* max_finite_int eb sb: ⌊MAX_FINITE⌋, used for RTP and RTN.         *)
(*                                                                     *)
(* The concrete computation is performed by mk_is_inf_of_int in        *)
(* fpa_rewriter.cpp using mpf_manager::mk_max_value and to_rational.  *)
(* ------------------------------------------------------------------ *)

assume val overflow_threshold : (eb: pos) -> (sb: pos) -> pos
assume val max_finite_int     : (eb: pos) -> (sb: pos) -> pos

(* RNE: overflow iff |x| >= overflow_threshold(eb, sb).
   At the boundary, RNE rounds to even; since MAX_FINITE has an odd
   significand, it rounds away from MAX_FINITE, i.e. to infinity. *)
assume val ax_is_inf_rne :
  #eb:pos -> #sb:pos -> (x: int) ->
  Lemma (is_inf (to_fp_of_int #eb #sb RNE x) =
         (x >= overflow_threshold eb sb || x <= -(overflow_threshold eb sb)))

(* RNA: same threshold as RNE (both round ties away from zero). *)
assume val ax_is_inf_rna :
  #eb:pos -> #sb:pos -> (x: int) ->
  Lemma (is_inf (to_fp_of_int #eb #sb RNA x) =
         (x >= overflow_threshold eb sb || x <= -(overflow_threshold eb sb)))

(* RTP: positive overflow only (x > MAX_FINITE rounds up to +∞;
   negative values are rounded toward zero, never to -∞). *)
assume val ax_is_inf_rtp :
  #eb:pos -> #sb:pos -> (x: int) ->
  Lemma (is_inf (to_fp_of_int #eb #sb RTP x) = (x > max_finite_int eb sb))

(* RTN: negative overflow only (x < -MAX_FINITE rounds down to -∞;
   positive values are rounded toward zero, never to +∞). *)
assume val ax_is_inf_rtn :
  #eb:pos -> #sb:pos -> (x: int) ->
  Lemma (is_inf (to_fp_of_int #eb #sb RTN x) = (x < -(max_finite_int eb sb)))

(* RTZ: truncation toward zero never overflows to infinity. *)
assume val ax_is_inf_rtz :
  #eb:pos -> #sb:pos -> (x: int) ->
  Lemma (is_inf (to_fp_of_int #eb #sb RTZ x) = false)
