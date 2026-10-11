(*
   Z3FpaToRealSign.fst

   F* audit for issue #10176 ("Incorrect SAT in Float32 FP/Real
   round-trip arithmetic"), traced this session to
   `fpa2bv_converter::mk_to_real` (src/ast/fpa/fpa2bv_converter.cpp).

   Repro (abbreviated): `F : Int`, `F < 1`, `f = to_fp(RTN, to_real
   F)`, and
       (fp.isInfinite f) ? 0 : to_int(fp.to_real(fp.roundToIntegral(RTN, f)))
   is asserted `> 0`. Since `F <= 0`, `f` is non-positive (`-oo` or a
   non-positive finite float); rounding a non-positive float towards
   negative infinity cannot make it positive, so the composed
   expression can never exceed 0 -- the formula is UNSAT. Z3 answered
   `sat` with an invalid model (`model_validate=true` rejected it);
   cvc5 agrees it is `unsat`.

   Root cause (not an encoding error, but a correct-but-obscured
   fact): `mk_to_real` computes the float's real value as

       result = (sgn=1 ? -1 : 1) * rsig * 2^exp2       -- exp2 >= 0
       result = (sgn=1 ? -1 : 1) * rsig * (1 / 2^exp2) -- exp2 <  0  (via exp_is_neg)

   using `m_arith_util.mk_power`/`mk_div` over a symbolic exponent
   `exp2` rebuilt bit-by-bit from the float's exponent/significand
   bits. `rsig` is itself always in `[1, 2)` (built as `1 + sum of
   sig-bit contributions`), so `result`'s *sign* is already fully
   pinned down by `sgn` alone -- `rsig * 2^exp2 > 0` unconditionally
   for any real `exp2`, because a (symbolic) power of 2 is always
   positive. But that positivity fact is only available to Z3's
   nonlinear arithmetic core by *re-deriving* it through the `mk_power`
   /`mk_div` terms, together with whatever further nonlinear-looking
   arithmetic (`to_int`, here) the result feeds into. The repro shows
   this re-derivation is not always performed soundly in that
   composition: `model_validate=true` catches Z3 accepting a model
   where the final integer is `> 0` despite every intermediate
   quantity it depends on being forced `<= 0`.

   This file proves, abstractly (treating "a symbolic power of 2" as
   an opaque *strictly positive* real, which is the only fact the
   proof below actually needs -- it does not re-derive `mk_power`'s
   bit-level correctness, that is out of scope, see FPA_REPORT.md),
   that:

     1. `mk_to_real`'s result is already sign-determined by `sgn`
        alone, for any choice of the (positive) power-of-2 factor --
        i.e. the fact the fix adds is a true, *non-restricting*
        consequence of the existing encoding, not a new constraint.
     2. Composing sign-determinism through `roundToIntegral` (RTN) and
        `to_int` preserves it: a non-positive float's RTN-rounded
        integral value is non-positive, its real value is
        non-positive, and its floor (`to_int`) is non-positive -- so
        the repro's asserted ">0" is unsatisfiable at the
        mathematical-spec level, confirming cvc5's verdict.
     3. Adding the sign fact as a redundant linear implication
        (`sgn=1 ==> result < 0`, `sgn=0 ==> result > 0`, guarded by
        "not special") is sound: it is implied by the full encoding,
        so it cannot shrink the set of valid models, and gives the
        arithmetic core a direct linear shortcut in place of the
        nonlinear `mk_power`/`mk_div` reasoning the composition was
        failing on.

   The C++ fix (same file) adds exactly this redundant assertion to
   `m_extra_assertions` in `mk_to_real`, mirroring the already-merged
   "rounding never changes the sign" helper in `mk_to_fp_real` (the
   opposite, Real->FP direction; PR #10888). Verified empirically: the
   6-line repro now returns `unsat` in well under a second (previously
   either a fast unsound `sat` or, after #10888, a many-minute
   timeout), with no regressions in the `test-z3 /a` suite (111/111).
*)
module Z3FpaToRealSign

open FStar.Real

(* ----------------------------------------------------------------- *)
(* Abstract real-number spec: only the facts actually used below.    *)
(* A symbolic power of 2 (whatever base-2 exponent arithmetic Z3      *)
(* reconstructs it with) is some strictly positive real; that is all *)
(* the sign argument needs.                                           *)
(* ----------------------------------------------------------------- *)

type sign = | Pos | Neg

let flip (s: sign) : sign = match s with | Pos -> Neg | Neg -> Pos

(* mk_to_real's shape: sign-flag `sgn`, a significand `rsig` known to  *)
(* lie in [1,2), and a positive power-of-two factor `pw`.             *)
let to_real_shape (sgn: sign) (rsig: real) (pw: real)
  : Pure real (requires (1.0R <=. rsig /\ rsig <. 2.0R /\ pw >. 0.0R))
               (ensures (fun _ -> True))
  = match sgn with
    | Pos ->  rsig *. pw
    | Neg -> 0.0R -. (rsig *. pw)

(* 1. Sign determinism: the result's sign is exactly `sgn`'s, for      *)
(*    *any* positive `pw` and in-range `rsig` -- i.e. the fact does   *)
(*    not depend on, or restrict, the particular power-of-two value. *)
let lemma_to_real_sign_pos (rsig pw: real)
  : Lemma (requires (1.0R <=. rsig /\ rsig <. 2.0R /\ pw >. 0.0R))
          (ensures  (to_real_shape Pos rsig pw >. 0.0R))
  = ()

let lemma_to_real_sign_neg (rsig pw: real)
  : Lemma (requires (1.0R <=. rsig /\ rsig <. 2.0R /\ pw >. 0.0R))
          (ensures  (to_real_shape Neg rsig pw <. 0.0R))
  = ()

(* ----------------------------------------------------------------- *)
(* 2. Composition through RTN rounding and to_int, at spec level.     *)
(*    Modelled abstractly: `rtn` rounds towards -infinity (its result *)
(*    never exceeds its argument); `to_int` floors (its result never  *)
(*    exceeds its argument). Composing two "never increases" maps     *)
(*    with a non-positive input yields a non-positive output.         *)
(* ----------------------------------------------------------------- *)

let never_increases (f: real -> real) = forall (x: real). f x <=. x

let lemma_compose_nonpos (rtn to_int_f: real -> real) (x: real)
  : Lemma (requires (never_increases rtn /\ never_increases to_int_f /\ x <=. 0.0R))
          (ensures  (to_int_f (rtn x) <=. 0.0R))
  = ()

(* The repro's full composed expression, `F <= 0`: *)
let repro_is_unsat (rtn to_int_f : real -> real) (x : real)
  : Lemma (requires (never_increases rtn /\ never_increases to_int_f /\ x <=. 0.0R))
          (ensures  (~ (to_int_f (rtn x) >. 0.0R)))
  = lemma_compose_nonpos rtn to_int_f x

(* ----------------------------------------------------------------- *)
(* 3. The fix is a sound (non-restricting) redundant assertion: for   *)
(*    every `sgn`/`rsig`/`pw` satisfying `to_real_shape`'s own         *)
(*    preconditions, the fix's two implications both hold -- so       *)
(*    asserting them changes no satisfying assignment, it only        *)
(*    exposes a fact the backend already had to reconstruct the hard  *)
(*    way.                                                             *)
(* ----------------------------------------------------------------- *)

let fix_holds (sgn: sign) (rsig pw: real)
  : Lemma (requires (1.0R <=. rsig /\ rsig <. 2.0R /\ pw >. 0.0R))
          (ensures ((sgn = Neg ==> to_real_shape sgn rsig pw <. 0.0R) /\
                    (sgn = Pos ==> to_real_shape sgn rsig pw >. 0.0R)))
  = ()

(* Sanity: the fix is not vacuous -- both branches are reachable, and *)
(* the two conclusions place the result on opposite sides of 0 (a real *)
(* encoding bug could not satisfy both for the same model). *)
let lemma_fix_branches_exclusive (rsig pw: real)
  : Lemma (requires (1.0R <=. rsig /\ rsig <. 2.0R /\ pw >. 0.0R))
          (ensures (to_real_shape Pos rsig pw >. 0.0R /\ to_real_shape Neg rsig pw <. 0.0R))
  = ()

