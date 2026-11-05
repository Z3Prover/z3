(*
   Z3FpaRoundingBits.fst

   This extends Z3FpaRoundingAudit.fst (which treated `gap_lo`/`gap_hi`
   as *abstract* positive rationals) with the one genuinely demanding
   fact it left unverified: that PR #10888's concrete "neighbor gap"
   *formulas* --

       gap_up   = is_exp_zero ? min_subnormal : |r| / sig_value
       gap_down = (is_exp_zero \/ is_exp_one \/ ~sig_is_zero)
                    ? gap_up : gap_up / 2

   -- actually compute the real distance from a representable value to
   its successor/predecessor, for *every* position in the format,
   including the two structurally different boundary cases the code
   singles out:

     (a) crossing a power-of-two binade boundary (where the ulp
         doubles, so the gap *below* the boundary is half the gap
         *above* it), and
     (b) the smallest-normal / largest-subnormal boundary (where,
         exceptionally, the gap is *not* halved, because subnormals
         share the smallest normal's ulp).

   Axiomatization strategy: rather than reproducing the bit-level
   `(sign, exponent, significand)` encoding exactly (that duplicates
   `Z3FpaConverter.fst`'s `bits` record and the unproved `unpack`/
   `round` circuitry), we axiomatize the *value semantics* directly:
   a representable magnitude at "format position" `(e, s)` has real
   value `s * 2^e / 2^common_shift`, where `common_shift` is a fixed,
   format-dependent constant (`bias + sbits - 1`) and `e`/`s` range so
   that:
     - `e = 1` together with `s` ranging over the *full*
       `[0, 2^sbits - 1]` window covers subnormals
       (`s < 2^(sbits-1)`), zero (`s = 0`), and the first normal
       binade (`s >= 2^(sbits-1)`) uniformly -- this single fact is
       exactly what makes the smallest-normal/largest-subnormal
       boundary "not special" mathematically (it is a same-exponent
       step, not a binade-boundary step);
     - `e >= 2` together with `s` ranging over `[2^(sbits-1), 2^sbits-1]`
       covers each subsequent normal binade.

   This is a faithful re-derivation of the standard IEEE-754 value
   mapping (checked by hand against `fpa2bv_converter.cpp`'s own
   `mk_bias`/subnormal-scale constants in `Z3FpaRoundingAudit.fst`'s
   `lemma_binade_carry_witness`), at one level of abstraction above
   the raw bit pattern -- adequate to verify the *real-arithmetic*
   content of the gap formulas, though not a replacement for actually
   verifying `unpack`/`round` bit-for-bit (still out of scope; see
   FPA_REPORT.md).
*)
module Z3FpaRoundingBits

open Z3FpaConverter       // pow2
open Z3FpaRoundingAudit   // rat, mk_int, mk_frac, rat_eq, rat_sub, rat_half, ...

(* ----------------------------------------------------------------- *)
(* pow2 arithmetic helpers (additive to Z3FpaConverter.fst, not         *)
(* modifying it).                                                       *)
(* ----------------------------------------------------------------- *)

let rec lemma_pow2_add (a b:nat)
  : Lemma (ensures pow2 (a + b) == pow2 a * pow2 b)
          (decreases a)
  = if a = 0 then () else lemma_pow2_add (a - 1) b

let lemma_pow2_succ (n:nat)
  : Lemma (pow2 (n + 1) == 2 * pow2 n)
  = lemma_pow2_add n 1

(* ----------------------------------------------------------------- *)
(* Rational multiplication (additive to Z3FpaRoundingAudit.fst).       *)
(* ----------------------------------------------------------------- *)

let rat_mul (a b:rat) : rat = { num = a.num * b.num; den = a.den * b.den }

(* ----------------------------------------------------------------- *)
(* The value mapping and the "unit" (ulp) at a given scale exponent.   *)
(* ----------------------------------------------------------------- *)

(* unit(cs, e) = 2^e / 2^cs -- the step size between consecutive
   representable magnitudes at scale exponent `e`. *)
let unit (cs e:nat) : rat = mk_frac (pow2 e) (pow2 cs)

(* val_of(cs, e, s) = s * unit(cs, e) -- the real value of the
   representable magnitude at "format position" (e, s). *)
let val_of (cs e s:nat) : rat = rat_mul (mk_int s) (unit cs e)

(* ----------------------------------------------------------------- *)
(* Base lemma 1: a same-exponent step (incrementing `s` by one at a    *)
(* fixed scale `e`) always advances the value by exactly `unit(cs,e)`. *)
(* This covers subnormal-to-subnormal steps, the subnormal-to-        *)
(* smallest-normal step, and every within-binade normal step.          *)
(* ----------------------------------------------------------------- *)

let lemma_succ_same_exp (cs e s:nat)
  : Lemma (rat_eq (rat_sub (val_of cs e (s + 1)) (val_of cs e s)) (unit cs e))
  = ()

(* ----------------------------------------------------------------- *)
(* Base lemma 2: crossing a binade boundary -- from the top of binade  *)
(* `e` (`s = 2^sigbits - 1`) to the bottom of binade `e+1`              *)
(* (`s = 2^(sigbits-1)`) -- always advances the value by exactly        *)
(* `unit(cs,e)`, i.e. *half* of `unit(cs,e+1)` (since                   *)
(* `unit(cs,e+1) = 2 * unit(cs,e)`, `lemma_pow2_succ`/`unit`'s          *)
(* definition). This is the mathematical content of "the gap below a   *)
(* power of two is half the gap above it".                             *)
(* ----------------------------------------------------------------- *)

let lemma_succ_binade_boundary (cs sigbits e:nat{sigbits >= 1})
  : Lemma (rat_eq (rat_sub (val_of cs (e + 1) (pow2 (sigbits - 1)))
                           (val_of cs e (pow2 sigbits - 1)))
                  (unit cs e))
  =
  lemma_pow2_add sigbits e;             // pow2(sigbits+e) == pow2 sigbits * pow2 e
  lemma_pow2_add (sigbits - 1) (e + 1)  // pow2(sigbits-1+e+1) == pow2(sigbits-1) * pow2(e+1)

let lemma_unit_doubles (cs e:nat)
  : Lemma (rat_eq (unit cs (e + 1)) (rat_mul (mk_int 2) (unit cs e)))
  = lemma_pow2_succ e

(* ----------------------------------------------------------------- *)
(* Successor / predecessor at "format position" (e, s), with            *)
(* `sigbits` the full-significand bit width (hidden bit included for    *)
(* normals; `e = 1` is the unified subnormal/first-binade scale, so no   *)
(* separate subnormal case is needed -- see module header).              *)
(* ----------------------------------------------------------------- *)

let is_top_of_binade (sigbits s:nat{sigbits >= 1}) : bool = s = pow2 sigbits - 1
let is_bottom_of_binade (sigbits s:nat{sigbits >= 1}) : bool = s = pow2 (sigbits - 1)

let succ_e (sigbits e s:nat{sigbits >= 1}) : nat =
  if is_top_of_binade sigbits s then e + 1 else e
let succ_s (sigbits s:nat{sigbits >= 1}) : nat =
  if is_top_of_binade sigbits s then pow2 (sigbits - 1) else s + 1

(* gap_up, exactly as in PR #10888: it is *always* unit(cs,e),
   regardless of whether `s` is at a binade boundary -- matching the
   code's "ulp = |r| / sig_value" formula, since val_of(cs,e,s) =
   s * unit(cs,e) by definition. *)
let gap_up (cs e:nat) : rat = unit cs e

let lemma_gap_up_is_successor_distance (cs sigbits e s:nat{sigbits >= 1 /\ e >= 1})
  : Lemma (rat_eq (rat_sub (val_of cs (succ_e sigbits e s) (succ_s sigbits s))
                           (val_of cs e s))
                  (gap_up cs e))
  =
  if is_top_of_binade sigbits s
  then lemma_succ_binade_boundary cs sigbits e
  else lemma_succ_same_exp cs e s

(* gap_down: halved at a binade boundary (relative to `gap_up` at the
   *current* scale `e`, i.e. `unit(cs,e)/2`, which equals `unit(cs,e-1)`
   since `unit` doubles with each `e` increment -- `lemma_unit_doubles`),
   *except* when `e = 1` (the smallest normal, whose predecessor -- the
   largest subnormal -- sits at the *same* scale `e = 1`, not `e = 0`:
   there is no "binade boundary" there at all, per the module-header
   unification). *)
let gap_down (cs sigbits e s:nat{sigbits >= 1}) : rat =
  if is_bottom_of_binade sigbits s && e >= 2
  then rat_half (unit cs e)
  else unit cs e

let pred_e (sigbits e s:nat{sigbits >= 1}) : nat =
  if is_bottom_of_binade sigbits s && e >= 2 then e - 1 else e
let pred_s (sigbits e s:nat{sigbits >= 1 /\ s >= 1}) : nat =
  if is_bottom_of_binade sigbits s && e >= 2 then pow2 sigbits - 1 else s - 1

let lemma_gap_down_is_predecessor_distance (cs sigbits e s:nat{sigbits >= 1 /\ s >= 1})
  : Lemma (rat_eq (rat_sub (val_of cs e s)
                           (val_of cs (pred_e sigbits e s) (pred_s sigbits e s)))
                  (gap_down cs sigbits e s))
  =
  if is_bottom_of_binade sigbits s && e >= 2 then begin
    let e' = e - 1 in
    assert (s == pow2 (sigbits - 1));
    assert (e' + 1 == e);
    // the boundary step from (e', top-of-binade) to (e'+1, bottom-of-binade)
    lemma_succ_binade_boundary cs sigbits e';
    // val_of cs (e'+1) (pow2(sigbits-1)) is definitionally val_of cs e s,
    // and val_of cs e' (pow2 sigbits - 1) is definitionally
    // val_of cs (pred_e ...) (pred_s ...), once e'+1 == e and
    // s == pow2(sigbits-1) are in scope (both asserted above), so the
    // lemma's conclusion already states:
    //   rat_eq (rat_sub (val_of cs e s) (val_of cs (pred_e..) (pred_s..)))
    //          (unit cs e')
    // It remains to relate unit(cs,e') to gap_down's rat_half(unit cs e).
    lemma_unit_doubles cs e';
    // rat_eq (unit cs e) (rat_mul 2 (unit cs e')), i.e. unit(cs,e') is
    // "half" of unit(cs,e) -- exactly rat_half(unit cs e) numerically.
    assert (rat_eq (unit cs e') (rat_half (unit cs e)))
  end
  else lemma_succ_same_exp cs e (s - 1)

(* ----------------------------------------------------------------- *)
(* Smallest-normal / largest-subnormal corollary, stated concretely:    *)
(* the gap from the smallest normal down to the largest subnormal is    *)
(* *not* halved (unlike every other binade-bottom point with e >= 2).   *)
(* This is the exact "except the smallest normal..." exception PR       *)
(* #10888 documents in its `gap_down` computation.                      *)
(* ----------------------------------------------------------------- *)

let lemma_smallest_normal_gap_not_halved (cs sigbits:nat{sigbits >= 1})
  : Lemma (let e = 1 in let s = pow2 (sigbits - 1) in
           rat_eq (gap_down cs sigbits e s) (unit cs e) /\     // not halved
           rat_eq (rat_sub (val_of cs e s) (val_of cs e (s - 1))) (gap_down cs sigbits e s))
  = lemma_succ_same_exp cs 1 (pow2 (sigbits - 1) - 1)
