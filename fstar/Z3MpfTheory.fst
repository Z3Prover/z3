(*
   Z3MpfTheory.fst

   Formalization of the representation invariants of `src/util/mpf.h`
   / `mpf.cpp` -- Z3's arbitrary-precision IEEE-754 floating-point
   library. Unlike `fpa2bv_converter.cpp` (fixed-width bit-vector
   circuits, audited in Z3FpaConverter.fst) or the symbolic rewriting
   in `fpa_rewriter.cpp` (Z3FpaRewrites.fst), `mpf` represents a float
   as a triple

       (sign : bool, significand : mpz, exponent : mpf_exp_t = int64)

   where `significand`/`exponent` are arbitrary-precision (no fixed
   bit-width in storage; `unpack`/`round` normalize to `sbits` bits
   only transiently during operations).

   This file covers the *value-level* ground truth that is common to
   every mpf operation:

     - the four `ebits`-indexed exponent landmarks `mk_bot_exp`,
       `mk_top_exp`, `mk_min_exp`, `mk_max_exp`, and the bias/unbias
       maps, transcribed directly from mpf.cpp:1839-1866;

     - the classification predicates `is_zero`/`is_nan`/`is_inf`/
       `is_normal`/`is_denormal`, transcribed directly from
       mpf.cpp:389-391 and mpf.cpp:1781-1803, together with a proof
       that they partition the reachable (exponent, significand)
       space exhaustively and disjointly;

     - the real-number value of an unpacked mpf, matching
       `mpf_manager::to_rational` (mpf.cpp:1705-1719) exactly, and a
       proof that it coincides with the `val_of` ground truth already
       used (as an independently-introduced abstraction) in
       Z3FpaRoundingBits.fst. This closes the loop between that
       earlier abstract model and the concrete library code.

   Out of scope here (see MPF_REPORT.md): the bit-shifting mechanics
   of `unpack`/`renormalize`/`round` that *compute* the significand
   and exponent fields in the first place (addressed, for the
   rounding-decision logic specifically, in Z3MpfRound.fst), and the
   full arithmetic pipelines of add_sub/mul/div/sqrt/fma/rem.
*)
module Z3MpfTheory

(* ----------------------------------------------------------------- *)
(* Self-contained integer power-of-two helper (mirrors the pattern    *)
(* used throughout the seq/fpa audits).                               *)
(* ----------------------------------------------------------------- *)

let rec pow2 (n:nat) : Tot pos =
  if n = 0 then 1 else 2 * pow2 (n - 1)

let rec lemma_pow2_monotone (a b:nat)
  : Lemma (requires a < b) (ensures pow2 a < pow2 b)
          (decreases b)
  = if b - a = 1 then () else lemma_pow2_monotone a (b - 1)

(* ----------------------------------------------------------------- *)
(* Exponent landmarks, transcribed verbatim from mpf.cpp:1839-1866.   *)
(* `ebits` is the number of exponent bits (SASSERT'd >= 2 for bot/top, *)
(* >= 1 for min/max in the source; we require >= 2 throughout, which   *)
(* covers every real use since IEEE formats all have ebits >= 2).     *)
(* ----------------------------------------------------------------- *)

let mk_bot_exp (ebits:nat{ebits >= 2}) : int = - (pow2 (ebits - 1) - 1)
let mk_top_exp (ebits:nat{ebits >= 2}) : int = pow2 (ebits - 1)
let mk_min_exp (ebits:nat{ebits >= 2}) : int = mk_bot_exp ebits + 1
let mk_max_exp (ebits:nat{ebits >= 2}) : int = pow2 (ebits - 1) - 1

let bias_exp (ebits:nat{ebits >= 2}) (unbiased:int) : int =
  unbiased + (pow2 (ebits - 1) - 1)
let unbias_exp (ebits:nat{ebits >= 2}) (biased:int) : int =
  biased - (pow2 (ebits - 1) - 1)

(* Theorem: bias_exp/unbias_exp are mutually inverse (mpf.cpp:1860-1865 *)
(* is a pure additive shift, so this is immediate, but it is exactly   *)
(* the fact `fpa2bv_converter.cpp`'s bit-vector bias/unbias circuit    *)
(* (already proved in Z3FpaConverter.fst) is supposed to implement).   *)
let lemma_bias_unbias_inverse (ebits:nat{ebits >= 2}) (u:int)
  : Lemma (unbias_exp ebits (bias_exp ebits u) = u)
  = ()

let lemma_unbias_bias_inverse (ebits:nat{ebits >= 2}) (b:int)
  : Lemma (bias_exp ebits (unbias_exp ebits b) = b)
  = ()

(* Theorem: the landmarks are strictly ordered, i.e. there is a        *)
(* nonempty "normal" range strictly between bot and top, consistent    *)
(* with mpf.cpp relying on `bot < min_exp <= max_exp < top` implicitly. *)
let lemma_exp_landmarks_ordered (ebits:nat{ebits >= 2})
  : Lemma (mk_bot_exp ebits < mk_min_exp ebits /\
           mk_min_exp ebits <= mk_max_exp ebits /\
           mk_max_exp ebits < mk_top_exp ebits)
  = ()  // pure linear arithmetic on the closed forms above.

(* ----------------------------------------------------------------- *)
(* Classification predicates, transcribed verbatim from                *)
(* mpf.cpp:389-391 (is_zero) and mpf.cpp:1781-1803                     *)
(* (is_nan/is_inf/is_normal/is_denormal). `sig` stands for the (always  *)
(* nonnegative) significand magnitude; `e` is the raw (unbiased, as     *)
(* stored in `mpf.exponent`) exponent field.                           *)
(* ----------------------------------------------------------------- *)

let has_bot_exp (ebits:nat{ebits >= 2}) (e:int) : bool = e = mk_bot_exp ebits
let has_top_exp (ebits:nat{ebits >= 2}) (e:int) : bool = e = mk_top_exp ebits

let is_zero_p     (ebits:nat{ebits >= 2}) (e:int) (sig:nat) : bool =
  has_bot_exp ebits e && sig = 0
let is_denormal_p (ebits:nat{ebits >= 2}) (e:int) (sig:nat) : bool =
  not (is_zero_p ebits e sig) && has_bot_exp ebits e
let is_normal_p   (ebits:nat{ebits >= 2}) (e:int) (sig:nat) : bool =
  not (has_top_exp ebits e || is_denormal_p ebits e sig || is_zero_p ebits e sig)
let is_nan_p      (ebits:nat{ebits >= 2}) (e:int) (sig:nat) : bool =
  has_top_exp ebits e && sig <> 0
let is_inf_p      (ebits:nat{ebits >= 2}) (e:int) (sig:nat) : bool =
  has_top_exp ebits e && sig = 0

(* Theorem: every (e, sig) with e in the representable range (which,    *)
(* per `has_top_exp`/`has_bot_exp`, is exactly [bot_exp, top_exp]) is    *)
(* classified into *exactly one* of the five categories. This is the    *)
(* mpf-level analogue of the bit-pattern exhaustiveness lemma already   *)
(* proved for the bit-vector encoding in Z3FpaConverter.fst.             *)
let lemma_classification_exhaustive_disjoint
    (ebits:nat{ebits >= 2}) (e:int{mk_bot_exp ebits <= e /\ e <= mk_top_exp ebits}) (sig:nat)
  : Lemma (ensures
      (* exhaustive: at least one holds *)
      (is_zero_p ebits e sig || is_denormal_p ebits e sig ||
       is_normal_p ebits e sig || is_nan_p ebits e sig || is_inf_p ebits e sig) /\
      (* pairwise disjoint *)
      (is_zero_p ebits e sig     ==> not (is_denormal_p ebits e sig || is_normal_p ebits e sig || is_nan_p ebits e sig || is_inf_p ebits e sig)) /\
      (is_denormal_p ebits e sig ==> not (is_zero_p ebits e sig || is_normal_p ebits e sig || is_nan_p ebits e sig || is_inf_p ebits e sig)) /\
      (is_normal_p ebits e sig   ==> not (is_zero_p ebits e sig || is_denormal_p ebits e sig || is_nan_p ebits e sig || is_inf_p ebits e sig)) /\
      (is_nan_p ebits e sig      ==> not (is_zero_p ebits e sig || is_denormal_p ebits e sig || is_normal_p ebits e sig || is_inf_p ebits e sig)) /\
      (is_inf_p ebits e sig      ==> not (is_zero_p ebits e sig || is_denormal_p ebits e sig || is_normal_p ebits e sig || is_nan_p ebits e sig)))
  = ()

(* ----------------------------------------------------------------- *)
(* Rational value semantics, transcribed verbatim from                 *)
(* `mpf_manager::to_rational` (mpf.cpp:1705-1719), applied to an        *)
(* already-`unpack`ed (normalize=true) representative: after unpack,    *)
(* a normal number's significand has the hidden bit added in, and a     *)
(* subnormal's significand/exponent have been shifted so that the       *)
(* significand occupies the full `sbits` width (mpf.cpp:1943-1955).     *)
(* In both cases the code computes                                      *)
(*                                                                      *)
(*     n = (+/-) significand,  d = 2^(sbits-1)                          *)
(*     value = n * 2^exponent / d     (if exponent >= 0)                *)
(*           = n / (d * 2^-exponent)  (if exponent <  0)                *)
(*                                                                      *)
(* which is the same closed-form value in both branches:                *)
(*     value = (-1)^sign * significand * 2^exponent / 2^(sbits-1)       *)
(*                                                                      *)
(* This is *exactly* the `val_of` ground truth introduced abstractly    *)
(* in Z3FpaRoundingBits.fst (`val_of cs e s = s * 2^e / 2^cs`, there     *)
(* with `cs = sbits - 1`) to reason about successor/predecessor gaps.   *)
(* We restate it here using a rational-number pair (num, den) to avoid  *)
(* a dependency on F*'s real numbers, matching the audit's established  *)
(* no-stdlib-reals style.                                               *)
(* ----------------------------------------------------------------- *)

type rat = { num: int; den: pos }

let rat_eq (a b:rat) : bool = a.num * b.den = b.num * a.den

(* `mpf_to_rational sign sig exponent sbits` : direct transcription of  *)
(* mpf.cpp:1705-1719's two branches (exponent >= 0 multiplies the       *)
(* numerator; exponent < 0 multiplies the denominator -- both encode    *)
(* the same rational number, which is the point of the lemma below).    *)
let mpf_to_rational (sign:bool) (sig:nat) (exponent:int) (sbits:pos{sbits >= 1})
  : rat =
  let n = if sign then - sig else sig in
  let d : pos = pow2 (sbits - 1) in
  if exponent >= 0 then
    { num = n * pow2 exponent; den = d }
  else
    { num = n; den = d * pow2 (- exponent) }

(* `val_of` as introduced in Z3FpaRoundingBits.fst, restated here        *)
(* locally (that file is self-contained and not opened, to keep this    *)
(* module independent); `cs = sbits - 1`. *)
let val_of (cs:nat) (e:int) (s:int) : rat =
  if e >= 0 then { num = s * pow2 e; den = pow2 cs }
  else { num = s; den = pow2 cs * pow2 (- e) }

(* Theorem: `to_rational`'s two case-split branches compute the same     *)
(* value as the unconditional closed form used throughout the FPA       *)
(* rounding-bits audit -- i.e. the concrete code's branch-by-the-sign-   *)
(* of-the-exponent strategy is value-preserving no matter which branch   *)
(* is taken, and coincides with `val_of`. *)
let lemma_to_rational_matches_val_of
    (sign:bool) (sig:nat) (exponent:int) (sbits:pos{sbits >= 1})
  : Lemma (rat_eq (mpf_to_rational sign sig exponent sbits)
                  (val_of (sbits - 1) exponent (if sign then - sig else sig)))
  = ()

(* Sanity instance: zero significand always yields value 0, regardless  *)
(* of exponent or sign -- i.e. `is_zero_p`/`is_pzero`/`is_nzero`'s        *)
(* "value 0" reading is consistent with the general value formula.      *)
let lemma_zero_significand_value_zero
    (sign:bool) (exponent:int) (sbits:pos{sbits >= 1})
  : Lemma (rat_eq (mpf_to_rational sign 0 exponent sbits) ({ num = 0; den = 1 }))
  = ()
