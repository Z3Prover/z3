(*
   Z3FpaRTNSelect.fst

   Targeted audit of the symbolic-rounding-mode *branch-selection*
   logic in `fpa2bv_converter::mk_to_fp_real_int`
   (src/ast/fpa/fpa2bv_converter.cpp, ~line 3188), motivated by open
   PR #11159 ("Correct RTN selection for real-to-float conversion").

   `mk_to_fp_real_int` converts a `(rm, int, real)` triple -- an
   exactly-known rational `q * 2^e` for a *concrete* integer exponent
   `e` and significand `q`, combined with a *symbolic* (unknown at
   conversion time) rounding-mode bitvector `bv_rm` -- into a
   floating-point bitvector. Because `e`/`q` are concrete, the
   converter can precompute the exactly-correctly-rounded result for
   *each* of the five IEEE rounding modes up front (`tn`, `tz`, `tp`,
   `nta`, `nte`, i.e. toward -inf/0/+inf, ties-to-away, ties-to-even)
   via the MPF library, and then build a `bv_rm`-indexed `ite` chain
   that *selects* among these five precomputed constants at the
   bit-vector level -- no further rounding arithmetic is needed, only
   correct selection.

   The bug (src/ast/fpa/fpa2bv_converter.cpp, line 3249, before the
   fix): the innermost selector condition `c1`, whose role is to
   distinguish the two modes *not* covered by `c2`/`c3`/`c4` (i.e.
   RTN vs RTZ) was written as

       c1 = m.mk_eq(bv_rm, m_bv_util.mk_numeral(BV_RM_TO_POSITIVE, 3));

   -- an exact duplicate of `c2`'s condition (`BV_RM_TO_POSITIVE`,
   i.e. RTP), instead of

       c1 = m.mk_eq(bv_rm, m_bv_util.mk_numeral(BV_RM_TO_NEGATIVE, 3));

   Since c2/c3/c4 take priority over c1 in the `ite` chain, `c1` is
   *only ever consulted* once `bv_rm` is known to be neither RTP, NTA,
   nor NTE -- i.e. precisely when `bv_rm` is RTN or RTZ. With the
   duplicated condition, that residual two-way choice always reduces
   to "is bv_rm == RTP?", which is now *vacuously false* in this
   branch (RTP was already handled earlier) -- so the chain always
   falls through to the `else` arm `bv_tz`, regardless of whether
   `bv_rm` is actually RTN or RTZ. Net effect: for every input where
   the rounding mode is symbolically forced to RTN (round toward
   negative infinity), the converter silently produces the *RTZ*
   (round toward zero) result instead -- wrong for any `q * 2^e < 0`
   that isn't exactly representable, where RTN and RTZ round in
   opposite directions. This exactly matches the regression test
   added by PR #11159 (`test_to_fp_real_int_symbolic_rtn`,
   src/test/fpa.cpp), which asserts `bv_rm` is forced to RTN (via
   `distinct m RNE RNA RTP RTZ`) and checks the result against the
   literal, independently-computed RTN bit pattern for `-0.1`.

   This file formalizes the five-way `ite`-chain selector abstractly
   (as a function of an opaque rounding-mode tag and five opaque
   per-mode result values), proves the buggy chain is *not* the
   identity selector at RTN (producing `tz` instead of `tn` whenever
   they differ), and proves the fixed chain *is* the identity selector
   for every rounding mode. The five precomputed MPF values themselves
   (and the surrounding `mk_numeral`/`mk_ite` bitvector encoding) are
   unmodeled, bit-precise machinery, exactly as in Z3FpaConverter.fst /
   FPA_REPORT.md's scope decision -- what is verified here is purely
   the *selection logic*, which is where the bug and the fix both
   live (a one-line diff, touching no arithmetic).
*)
module Z3FpaRTNSelect

(* The five IEEE-754 rounding modes, as distinguished by `bv_rm`'s
   3-bit encoding (BV_RM_TIES_TO_EVEN / BV_RM_TIES_TO_AWAY /
   BV_RM_TO_POSITIVE / BV_RM_TO_NEGATIVE / BV_RM_TO_ZERO). *)
type rm = | NTE | NTA | RTP | RTN | RTZ

(* ----------------------------------------------------------------- *)
(* The specification: for any choice of five per-mode result values,   *)
(* the correct selector just picks out the one matching `r`.          *)
(* ----------------------------------------------------------------- *)
let spec (#a:Type) (r:rm) (tn tz tp nta nte: a) : a =
  match r with
  | RTN -> tn
  | RTZ -> tz
  | RTP -> tp
  | NTA -> nta
  | NTE -> nte

(* ----------------------------------------------------------------- *)
(* The OLD (buggy) ite chain, transcribed verbatim from              *)
(* fpa2bv_converter.cpp lines 3246-3252 (pre-#11159):                 *)
(*                                                                      *)
(*   c1 = (bv_rm == RTP)       <-- bug: duplicate of c2                *)
(*   c2 = (bv_rm == RTP)                                               *)
(*   c3 = (bv_rm == NTA)                                               *)
(*   c4 = (bv_rm == NTE)                                               *)
(*   result = c1 ? tn : tz                                             *)
(*   result = c2 ? tp : result                                         *)
(*   result = c3 ? nta : result                                        *)
(*   result = c4 ? nte : result                                        *)
(*                                                                      *)
(* i.e. (reading outermost/highest-priority first):                    *)
(*   if c4 then nte else if c3 then nta else if c2 then tp              *)
(*   else if c1 then tn else tz                                        *)
(* ----------------------------------------------------------------- *)
let select_old (#a:Type) (r:rm) (tn tz tp nta nte: a) : a =
  let c1 = (r = RTP) in
  let c2 = (r = RTP) in
  let c3 = (r = NTA) in
  let c4 = (r = NTE) in
  if c4 then nte
  else if c3 then nta
  else if c2 then tp
  else if c1 then tn
  else tz

(* ----------------------------------------------------------------- *)
(* The FIXED chain (PR #11159): identical except c1 now tests RTN.    *)
(* ----------------------------------------------------------------- *)
let select_fixed (#a:Type) (r:rm) (tn tz tp nta nte: a) : a =
  let c1 = (r = RTN) in
  let c2 = (r = RTP) in
  let c3 = (r = NTA) in
  let c4 = (r = NTE) in
  if c4 then nte
  else if c3 then nta
  else if c2 then tp
  else if c1 then tn
  else tz

(* ----------------------------------------------------------------- *)
(* Theorem 1 (the fix is correct): `select_fixed` agrees with `spec`   *)
(* for *every* rounding mode and every choice of per-mode values.      *)
(* Decidable by case analysis on the 5-constructor `rm` (F*'s `match`  *)
(* in `spec`/`select_fixed` normalizes both sides definitionally).    *)
(* ----------------------------------------------------------------- *)
let lemma_fixed_correct (#a:Type) (r:rm) (tn tz tp nta nte: a)
  : Lemma (select_fixed r tn tz tp nta nte == spec r tn tz tp nta nte)
  = ()

(* ----------------------------------------------------------------- *)
(* Theorem 2 (the bug, precisely located): `select_old` disagrees      *)
(* with `spec` *only* at RTN (all other four modes are handled by     *)
(* c2/c3/c4, which the bug never touched), and there it always        *)
(* returns `tz` instead of the correct `tn`.                          *)
(* ----------------------------------------------------------------- *)
let lemma_old_wrong_at_rtn (#a:Type) (tn tz tp nta nte: a)
  : Lemma (select_old RTN tn tz tp nta nte == tz /\
           spec RTN tn tz tp nta nte == tn)
  = ()

(* Corollary: whenever the RTN and RTZ precomputed results actually
   differ (the only case where the bug has observable consequences --
   e.g. any negative, inexactly-representable `q * 2^e`, as in PR
   #11159's regression test with `q * 2^e = -0.1`), the old chain's
   output is provably wrong. *)
let lemma_old_unsound_when_distinguishable (#a:Type) (tn tz tp nta nte: a)
  : Lemma (requires tn =!= tz)
          (ensures select_old RTN tn tz tp nta nte =!= spec RTN tn tz tp nta nte)
  = ()

(* ----------------------------------------------------------------- *)
(* Theorem 3 (no regression elsewhere): for the other four modes, the  *)
(* old and fixed chains coincide -- the fix is a strictly local         *)
(* correction, touching only the RTN case, consistent with the PR's     *)
(* one-line diff and its regression test leaving all other rounding     *)
(* modes' behavior unchanged.                                           *)
(* ----------------------------------------------------------------- *)
let lemma_agree_off_rtn (#a:Type) (r:rm) (tn tz tp nta nte: a)
  : Lemma (requires r <> RTN)
          (ensures select_old r tn tz tp nta nte == select_fixed r tn tz tp nta nte)
  = ()
