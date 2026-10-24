(*
   Z3MpfRoundToIntegral.fst

   GitHub issue #11139: "fp.roundToIntegral rounds the FP(2,3)
   subnormal 1/4 to 1 in nearest modes".

   `mpf_manager::round_to_integral` (src/util/mpf.cpp, nearest-mode
   branch) and `fpa2bv_converter::mk_round_to_integral`
   (src/ast/fpa/fpa2bv_converter.cpp) both decide, for a value with
   magnitude in `[0,1)`, whether the correctly-rounded integer result
   is `0` or `1`, by comparing the value's *stored* exponent field
   directly against the literal `-1` (tie) / `< -1` (definitely below
   half). This hardcoded test is valid for *normal* numbers, where
   `exponent = -1` can only mean "magnitude in `[0.5,1)`, hidden bit
   present". It is NOT valid for *denormals*: mpf.cpp stores every
   denormal with the same sentinel exponent value `mk_bot_exp(ebits)`
   regardless of the denormal's true magnitude (the stored significand
   is the raw, un-renormalized fraction, with no hidden bit). For
   `ebits = 2`, `mk_bot_exp(2) = -1` -- the sentinel collides exactly
   with the hardcoded tie-test constant, so the unmodified code
   silently misclassifies every nonzero-significand denormal of a
   2-exponent-bit format, regardless of its true magnitude. For
   `ebits >= 3`, `mk_bot_exp(ebits) <= -2 < -1`, so the (buggy) literal
   `< -1` test always fires and happens to produce the right answer
   (every such denormal truly is `< 1/2`) -- which is exactly why the
   issue reports only the tiny custom formats FP(2,3)/FP(2,5)/FP(2,9)
   as affected, and why standard float16/32/64/128 (`ebits in
   {5,8,11,15}`) are immune.

   This file formalizes both the broken, stored-exponent-only decision
   procedure (`stored_round_up`, a transcription of the code as it was
   before the fix landed) and the fixed, renormalized-exponent decision
   procedure (`renorm_round_up`, a transcription of the fix applied in
   this commit to both mpf.cpp and fpa2bv_converter.cpp), against an
   independent ground truth for "should round_to_integral(RNE/RNA, v)
   produce 1 rather than 0" built directly from the exact rational
   value of a denormal. It proves:

     - `lemma_old_decision_wrong_11139`: the OLD decision procedure is
       WRONG for the issue's exact counterexample (FP(2,3), stored
       fraction 1, true value 1/4) -- a direct, mechanized confirmation
       that the issue is a real bug, not filed in error.

     - `lemma_old_decision_correct_for_ebits_ge_3`: the OLD decision
       procedure is nonetheless ALWAYS correct whenever `ebits >= 3`,
       because every denormal of such a format is unconditionally
       `< 1/2` -- explaining the issue's reported "Scope" exactly, from
       first principles rather than by enumeration.

     - `lemma_new_decision_correct`: the NEW (fixed) decision
       procedure, which renormalizes the stored (exponent, fraction)
       pair before comparing, is correct for every denormal of every
       format `ebits >= 2`, `sbits >= 2`, closing the gap the old
       procedure had for `ebits = 2`.

   Scope note: as in Z3MpfRound.fst / Z3MpfExact.fst, the renormalization
   *shift amount* itself (how many bit-positions a given nonzero
   fraction must be shifted to reach the hidden-bit position) is
   bit-shifting mechanics; here it is captured directly as the
   mathematical relation "the renormalized exponent is the unique `e`
   with `pow2 (sbits-1) <= frac * pow2 (sbits-1-e-min_exp_power) <
   pow2 sbits`" -- see `is_renormalized_of` below -- rather than
   reproving the shift loop, consistent with how mpf.cpp's own fix
   reuses the already-proved/tested `renormalize()` helper instead of
   re-deriving it.
*)
module Z3MpfRoundToIntegral

open Z3MpfTheory    // pow2, mk_bot_exp, mk_min_exp
open Z3MpfRound      // rat, rat_eq/rat_lt/rat_le, rounding_mode, correct_inc

(* ----------------------------------------------------------------- *)
(* A dyadic rational `num * 2^e` (`num:nat`, `e:int` arbitrary), kept  *)
(* as an exact `rat` via a case split on the sign of `e` (needed only  *)
(* to keep the denominator a `pos`); and the key algebraic fact this   *)
(* whole proof rests on: scaling `num` up by `2^s` and `e` down by the *)
(* same `s` represents the same value (this is *exactly* what          *)
(* `renormalize()`'s left-shift-and-decrement-exponent loop does).      *)
(* ----------------------------------------------------------------- *)

let rat_from_pow2 (num:nat) (e:int) : rat =
  if e >= 0 then mk_frac (num * pow2 e) 1 else mk_frac num (pow2 (- e))

(* Additivity of `pow2`, proved directly (the analogous lemma exists in
   other audit files, but each is stated over its own module-local
   `pow2`, so we re-derive the one-line induction here rather than rely
   on an incidental defeq between distinct recursive definitions). *)
let rec lemma_pow2_add (a b:nat)
  : Lemma (ensures pow2 (a + b) == pow2 a * pow2 b)
  = if a = 0 then () else lemma_pow2_add (a - 1) b

let lemma_rat_from_pow2_scale (num:nat) (e:int) (s:nat)
  : Lemma (rat_eq (rat_from_pow2 num e) (rat_from_pow2 (num * pow2 s) (e - s)))
  =
  if e >= 0 && e - s >= 0 then
    lemma_pow2_add s (e - s)                 // pow2 e = pow2 s * pow2 (e-s)
  else if e >= 0 (* e - s < 0 *) then
    lemma_pow2_add e (s - e)                 // pow2 s = pow2 e * pow2 (s-e)
  else if e - s >= 0 then
    ()                                       // vacuous: e<0, s:nat, e-s>=0 is contradictory
  else
    lemma_pow2_add s (- e)                   // pow2 (s-e) = pow2 s * pow2 (-e)

(* ----------------------------------------------------------------- *)
(* A denormal's raw stored fraction (sbits-1 bits) and its exact       *)
(* rational value, transcribed from `mpf_manager::to_rational`'s        *)
(* denormal branch (mpf.cpp ~1705-1719): value = frac / 2^(sbits-1) *   *)
(* 2^(min_exp) = frac * 2^(min_exp - (sbits-1)).                        *)
(* ----------------------------------------------------------------- *)

let lemma_pow2_monotone_le (a b:nat{a <= b})
  : Lemma (ensures pow2 a <= pow2 b)
  = if a = b then () else Z3MpfTheory.lemma_pow2_monotone a b

(* Every denormal of every format (`ebits >= 2`) genuinely has
   magnitude in `[0,1)`: `mk_min_exp ebits <= 0` always (it is `0`
   exactly for `ebits = 2`, strictly negative otherwise), so the
   exponent `e` below is always `<= -(sbits-1) < 0`, and `frac <
   2^(sbits-1) <= 2^(-e)` (monotonicity) gives `frac / 2^(-e) < 1`
   directly. This is proved *generally* (not just for `ebits >= 3`),
   so `denormal_value`'s result type can carry the refinement
   `correct_round_up` needs at every call site, instead of re-deriving
   it ad hoc per lemma. *)
let lemma_denormal_value_range
    (ebits sbits:nat{ebits >= 2 /\ sbits >= 2}) (frac:nat{frac < pow2 (sbits - 1)})
  : Lemma (
      let e = mk_min_exp ebits - (sbits - 1) in
      rat_le zero (rat_from_pow2 frac e) /\ rat_lt (rat_from_pow2 frac e) (mk_int 1)
    )
  =
  let me = mk_min_exp ebits in
  let e = me - (sbits - 1) in
  assert (e < 0);
  assert (sbits - 1 <= - e);
  lemma_pow2_monotone_le (sbits - 1) (- e)
  // `pow2 (sbits-1) <= pow2 (-e)`, combined with `frac < pow2
  // (sbits-1)`, gives `frac < pow2 (-e)`, i.e. (since `e < 0`,
  // `rat_from_pow2 frac e = mk_frac frac (pow2 (-e))`) exactly
  // `rat_lt (rat_from_pow2 frac e) (mk_int 1)`.

let denormal_value (ebits sbits:nat{ebits >= 2 /\ sbits >= 2})
                    (frac:nat{frac < pow2 (sbits - 1)})
  : v:rat{rat_le zero v /\ rat_lt v (mk_int 1)}
  =
  lemma_denormal_value_range ebits sbits frac;
  rat_from_pow2 frac (mk_min_exp ebits - (sbits - 1))

(* The same "value = (hidden-bit-inserted significand) * 2^(exp -
   (sbits-1))" reading, but for an already-renormalized
   (exponent, fraction) pair -- i.e. the standard *normal*-number value
   formula, exactly as used throughout the other FP audits (e.g.
   Z3FpaTheory.fst's `val_of`). *)
let renormalized_value (sbits:nat{sbits >= 2}) (eff_exp:int) (eff_frac:nat{eff_frac < pow2 (sbits - 1)})
  : rat
  =
  rat_from_pow2 (eff_frac + pow2 (sbits - 1)) (eff_exp - (sbits - 1))

(* ----------------------------------------------------------------- *)
(* OLD (buggy) decision: literal transcription of the pre-fix code,   *)
(* which never renormalizes -- it tests the *stored* sentinel          *)
(* exponent `mk_bot_exp ebits` directly against `-1`/`< -1`, exactly   *)
(* as `round_to_integral`'s nearest-mode branch and                   *)
(* `mk_round_to_integral`'s `t2`/`c423` did before this commit.        *)
(* ----------------------------------------------------------------- *)

(* The nearest-mode branch of `round_to_integral` (mpf.cpp) and of
   `mk_round_to_integral` (fpa2bv_converter.cpp) is a single shared
   code block handling exactly these two rounding modes together
   (directed modes RTP/RTN/RTZ are dispatched to entirely different
   code paths elsewhere in both functions, untouched by this bug/fix,
   so they are intentionally not modeled here -- see MPF_REPORT.md). *)
type nearest_mode =
  | NTE
  | NTA

let as_rm (m:nearest_mode) : rounding_mode = match m with NTE -> RNE | NTA -> RNA

let stored_tie (ebits sbits:nat{ebits >= 2 /\ sbits >= 2}) (frac:nat{frac < pow2 (sbits - 1)}) : bool =
  mk_bot_exp ebits = -1 && frac = 0

let stored_below_half (ebits:nat{ebits >= 2}) : bool =
  mk_bot_exp ebits < -1

// `last` (parity of the kept integer) is always `false` here: in the
// "magnitude < 1" branch of round_to_integral the kept integer is
// always 0 (even), for both old and new code -- this is not part of
// the bug, so we fix it rather than parameterize over it.
let stored_round_up (ebits sbits:nat{ebits >= 2 /\ sbits >= 2})
                     (m:nearest_mode) (frac:nat{frac < pow2 (sbits - 1)})
  : bool
  =
  if stored_tie ebits sbits frac then
    (match m with NTE -> false | NTA -> true)
  else if stored_below_half ebits then
    false
  else
    true

(* ----------------------------------------------------------------- *)
(* NEW (fixed) decision: renormalize first. `is_renormalized_of`        *)
(* specifies what the fix's `renormalize()` call computes: the unique   *)
(* `(eff_exp, eff_frac)` such that shifting `frac` left by               *)
(* `me - eff_exp` places its leading 1 bit exactly at the hidden-bit    *)
(* position (`pow2 (sbits-1) <= shifted < pow2 sbits`), and `eff_frac`   *)
(* is that shifted value with the hidden bit stripped back out, i.e.    *)
(* exactly the fix applied to mpf.cpp / fpa2bv_converter.cpp.           *)
(* ----------------------------------------------------------------- *)

(* `shift` (the nonnegative number of bit-positions the fix's
   `renormalize()` call shifts `frac` left by) is taken as an explicit
   `nat` parameter -- rather than derived as `me - eff_exp` -- purely
   so every exponent used below stays a `pow2`-compatible value;
   `eff_exp` is then *defined* as `me - shift`, matching exactly how
   the real `renormalize()` loop decrements the exponent once per left
   shift. The defining equation `frac * 2^shift = eff_frac + 2^(sbits-1)`
   says: shifting the raw fraction left by `shift` places its leading 1
   bit exactly where the hidden bit belongs, and `eff_frac` is what
   remains after subtracting that hidden bit back out -- precisely
   `renormalize()`'s postcondition. *)
let is_renormalized_of (sbits:nat{sbits >= 2}) (frac:pos)
                        (shift:nat) (eff_frac:nat)
  : prop
  =
  frac * pow2 shift = eff_frac + pow2 (sbits - 1) /\
  eff_frac < pow2 (sbits - 1)

let new_tie (eff_exp:int) (eff_frac:nat) : bool = eff_exp = -1 && eff_frac = 0
let new_below_half (eff_exp:int) : bool = eff_exp < -1

let renorm_round_up (m:nearest_mode) (eff_exp:int) (eff_frac:nat) : bool =
  if new_tie eff_exp eff_frac then
    (match m with NTE -> false | NTA -> true)
  else if new_below_half eff_exp then
    false
  else
    true

(* ----------------------------------------------------------------- *)
(* Independent ground truth, reusing Z3MpfRound's already-proved        *)
(* `correct_inc` (sign=false, last=false: the kept integer is always    *)
(* 0, which is even) applied to the *exact* rational value of the      *)
(* denormal.                                                            *)
(* ----------------------------------------------------------------- *)

let correct_round_up (m:nearest_mode) (v:rat{rat_le zero v /\ rat_lt v (mk_int 1)}) : bool =
  correct_inc (as_rm m) false false v

(* ===================================================================
   Theorem 1 (bug confirmation): the OLD decision is WRONG for the
   issue's exact witness -- FP(2,3), stored fraction 1 (true value
   1/4), RNE and RNA.
   =================================================================== *)

let lemma_old_decision_wrong_11139 ()
  : Lemma (
      let v = denormal_value 2 3 1 in           // 1/4, as in the issue
      rat_eq v (mk_frac 1 4) /\
      stored_round_up 2 3 NTE 1 <> correct_round_up NTE v /\   // old: true, correct: false
      stored_round_up 2 3 NTA 1 <> correct_round_up NTA v      // old: true, correct: false
    )
  =
  ()

(* A second, sharper witness: the OLD code also mishandles the actual
   *tie* case (frac = 2, true value exactly 1/2) under RNE, because its
   tie test additionally requires `frac = 0` (valid for normals, where
   an all-zero fraction with exponent -1 is the *only* way to represent
   exactly 1/2) -- for this denormal format, `frac = 2` is the one that
   is exactly 1/2, not `frac = 0`. *)
let lemma_old_decision_wrong_on_true_tie ()
  : Lemma (
      let v = denormal_value 2 3 2 in
      rat_eq v (mk_frac 1 2) /\
      stored_round_up 2 3 NTE 2 <> correct_round_up NTE v      // old: true (not recognized as tie), correct: false (tie-to-even)
    )
  = ()

(* ===================================================================
   Theorem 2 (scope explanation): the OLD decision is nonetheless
   ALWAYS correct once `ebits >= 3`, because then `mk_bot_exp ebits <=
   -2`, so every denormal of that format has stored_below_half = true,
   and every denormal's true value genuinely is < 1/2 -- matching the
   issue's own report that float16/32/64/128 are unaffected.
   =================================================================== *)

let lemma_bot_exp_small_when_ebits_ge_3 (ebits:nat{ebits >= 3})
  : Lemma (mk_bot_exp ebits <= -2)
  = Z3MpfTheory.lemma_pow2_monotone 1 (ebits - 1)   // pow2 1 < pow2 (ebits-1), i.e. 2 < pow2(ebits-1), so bot_exp <= -2

let lemma_denormal_lt_half_when_ebits_ge_3
    (ebits sbits:nat{ebits >= 3 /\ sbits >= 2}) (frac:nat{frac < pow2 (sbits - 1)})
  : Lemma (rat_lt (denormal_value ebits sbits frac) half)
  =
  lemma_bot_exp_small_when_ebits_ge_3 ebits;
  let me = mk_min_exp ebits in
  let e = me - (sbits - 1) in
  // `me <= -1` (just proved), `sbits - 1 >= 1`, so `e <= -2 < 0`; and
  // `-e >= sbits` since `-e = (sbits-1) - me >= (sbits-1) + 1 = sbits`.
  assert (e < 0);
  assert (sbits <= - e);
  lemma_pow2_monotone_le sbits (- e)
  // `pow2 sbits <= pow2 (-e)`; combined with `frac < pow2 (sbits-1)`
  // (so `frac * 2 < pow2 sbits`) and `denormal_value ebits sbits frac
  // = rat_from_pow2 frac e = mk_frac frac (pow2 (-e))` (since `e < 0`),
  // `rat_lt (mk_frac frac (pow2 (-e))) half` unfolds to exactly
  // `frac * 2 < pow2 (-e)`, which Z3 now closes directly.

let lemma_old_decision_correct_for_ebits_ge_3
    (ebits sbits:nat{ebits >= 3 /\ sbits >= 2}) (m:nearest_mode) (frac:nat{frac < pow2 (sbits - 1)})
  : Lemma (stored_round_up ebits sbits m frac = correct_round_up m (denormal_value ebits sbits frac))
  =
  lemma_denormal_lt_half_when_ebits_ge_3 ebits sbits frac;
  lemma_bot_exp_small_when_ebits_ge_3 ebits;
  assert (rat_lt half (mk_int 1));
  assert (rat_lt (denormal_value ebits sbits frac) (mk_int 1));
  match m with NTE -> () | NTA -> ()
  // stored_below_half ebits = true (mk_bot_exp ebits <= -2 < -1) so
  // stored_round_up takes its "false" branch unconditionally; the
  // ground truth also says "false" since value < 1/2 in every mode.

(* ===================================================================
   Theorem 3 (fix correctness): the NEW, renormalized decision is
   correct for every denormal of every format, not just ebits >= 3.
   =================================================================== *)

(* Two congruence facts, proved directly over the `rat` cross-
   multiplication representation (not a general toolkit, just the two
   instances this proof needs: `rat_eq`-equal values agree on being
   `< half` and on being `= half`). Both reduce to pure linear/
   nonlinear integer arithmetic that Z3 discharges directly given
   positivity of both denominators. *)
let lemma_rat_eq_congr_lt_half (a b:rat)
  : Lemma (requires rat_eq a b) (ensures rat_lt a half = rat_lt b half)
  = ()

let lemma_rat_eq_congr_eq_half (a b:rat)
  : Lemma (requires rat_eq a b) (ensures rat_eq a half = rat_eq b half)
  = ()

let lemma_new_decision_correct
    (ebits sbits:nat{ebits >= 2 /\ sbits >= 2}) (m:nearest_mode)
    (frac:pos{frac < pow2 (sbits - 1)})
    (shift:nat) (eff_frac:nat{is_renormalized_of sbits frac shift eff_frac})
  : Lemma (renorm_round_up m (mk_min_exp ebits - shift) eff_frac = correct_round_up m (denormal_value ebits sbits frac))
  =
  let me = mk_min_exp ebits in
  let eff_exp = me - shift in
  // `shift` cannot be 0: that would force `frac = eff_frac + 2^(sbits-1)
  // >= 2^(sbits-1)`, contradicting `frac < 2^(sbits-1)`.
  assert (shift > 0);
  // Reading of `denormal_value` as `rat_from_pow2 frac (me-(sbits-1))`,
  // scaled by the renormalization shift, lands exactly on
  // `renormalized_value sbits eff_exp eff_frac` (both sides are
  // `rat_from_pow2` of the *same* nat, `eff_frac + 2^(sbits-1)`, by
  // `is_renormalized_of`'s defining equation, at the *same* exponent
  // `me - (sbits-1) - shift = eff_exp - (sbits-1)`).
  lemma_rat_from_pow2_scale frac (me - (sbits - 1)) shift;
  assert (rat_eq (denormal_value ebits sbits frac) (renormalized_value sbits eff_exp eff_frac));
  let v = denormal_value ebits sbits frac in
  let w = renormalized_value sbits eff_exp eff_frac in
  lemma_rat_eq_congr_lt_half v w;
  lemma_rat_eq_congr_eq_half v w;
  // `eff_exp <= mk_bot_exp ebits <= -1` always (since `shift >= 1`), so
  // the only two reachable regions are `eff_exp = -1` and
  // `eff_exp < -1` -- matching `renorm_round_up`'s case split exactly,
  // and ruling out the third ("eff_exp >= 0") region `correct_inc`
  // doesn't need to consider here.
  assert (eff_exp <= -1);
  if eff_exp < -1 then begin
    // w = (eff_frac + 2^(sbits-1)) * 2^(eff_exp-(sbits-1)) < 2^(eff_exp+1) <= 1/2.
    assert (eff_exp <= -2);
    let d : nat = sbits - 1 - eff_exp in
    assert (sbits + 1 <= d);
    lemma_pow2_monotone_le (sbits + 1) d;
    assert (rat_lt w half)
  end else begin
    // eff_exp = -1 exactly: w = (eff_frac + 2^(sbits-1)) / 2^sbits;
    // this is = 1/2 iff eff_frac = 0, and > 1/2 otherwise.
    assert (eff_exp = -1);
    if eff_frac = 0 then assert (rat_eq w half) else assert (rat_lt half w)
  end;
  match m with NTE -> () | NTA -> ()

(* ----------------------------------------------------------------- *)
(* Concrete corollary: the fix is correct on the issue's own witness.  *)
(* `frac = 1` (true value 1/4) renormalizes to `eff_exp = -2,           *)
(* eff_frac = 0` (1/4 = 1.0 * 2^-2), which both `renorm_round_up` and   *)
(* `correct_round_up` agree rounds DOWN to 0 -- matching the fixed       *)
(* z3.exe's observed `(_ +zero 2 3)` output and the issue's expected    *)
(* `sat` result.                                                        *)
(* ----------------------------------------------------------------- *)

let lemma_fix_closes_11139 ()
  : Lemma (
      is_renormalized_of 3 1 2 0 /\
      renorm_round_up NTE (mk_min_exp 2 - 2) 0 = false /\
      renorm_round_up NTA (mk_min_exp 2 - 2) 0 = false /\
      correct_round_up NTE (denormal_value 2 3 1) = false /\
      correct_round_up NTA (denormal_value 2 3 1) = false
    )
  = ()
