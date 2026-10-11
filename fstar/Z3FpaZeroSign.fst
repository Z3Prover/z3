(*
   Z3FpaZeroSign.fst

   Targeted audit of issue #7431 ("Invalid model issue on float
   formula"): `(_ to_fp 2 6) RTZ v = (fp (_ bv1 1) (_ bv0 2) (_ bv0 5))`
   (i.e. "does some real `v` round, under RTZ, to *negative* zero?")
   is reported `sat` with an invalid model.

   Root cause, pinned down directly in
   `fpa2bv_converter::mk_to_fp_real` (src/ast/fpa/fpa2bv_converter.cpp,
   symbolic-`x` branch, current master, *unaffected* by PRs #10888 and
   #10938 -- both retain this line verbatim):

       // x = 0 -> result = +0/-0
       m_extra_assertions.push_back(m.mk_implies(m.mk_eq(x, zero),
           m.mk_or(m.mk_eq(result, pzero), m.mk_eq(result, nzero))));

   This is the *only* constraint tying `x = 0` to the sign of a
   zero result. It is satisfied by `result = nzero` just as much as by
   `result = pzero` -- i.e. it is logically **equivalent to no
   constraint on the sign at all** once the rest of the function has
   already pinned `result` down to *some* zero (which it does: the
   exact-round-trip equation `to_real(result) = x` forces
   `to_real(result) = 0`, and only `pzero`/`nzero` have real value 0).

   But IEEE-754 conversion from a signless mathematical real has only
   one correct answer: `0 -> +0`, under *every* rounding mode (RTZ,
   RTN, RTP, RNE, RNA alike) -- a real number carries no sign bit to
   round "toward" or "away from", so there is nothing for the
   rounding mode to decide. The code's own comment ("result =
   +0/-0") already signals the gap: it should read "result = +0".

   This file proves, at the level of the two-element "zero kind"
   domain the constraint actually ranges over, that:

     1. the current code's disjunctive constraint is *vacuous*: it
        rules out nothing, so `result = nzero` remains consistent with
        it, reproducing the reported invalid model exactly;
     2. the obvious fix -- replacing the disjunction with the single
        equation `result = pzero` -- is **strictly stronger**, rules
        out exactly the bad model, and still admits the one genuinely
        correct witness (`result = pzero`).
*)
module Z3FpaZeroSign

(* ----------------------------------------------------------------- *)
(* The "kind" of a float result once it is known to be some zero      *)
(* (i.e. the case already isolated by `x = 0` together with the       *)
(* exact-round-trip equation and the `not(isnan result)` assertion).  *)
(* ----------------------------------------------------------------- *)

type zkind = | PZero | NZero

(* Ground truth (IEEE-754, independent of rounding mode): converting
   the real number 0 must yield +0. *)
let ieee_ground_truth (z:zkind) : prop = z == PZero

(* ----------------------------------------------------------------- *)
(* The CURRENT code's constraint, exactly as asserted (the two-way     *)
(* disjunction), reinterpreted as a predicate on `zkind`.               *)
(* ----------------------------------------------------------------- *)

let old_constraint (z:zkind) : bool =
  (z = PZero) || (z = NZero)

(* `old_constraint` is a tautology on `zkind` -- it holds for BOTH     *)
(* constructors, hence restricts nothing. This is the precise sense    *)
(* in which the current code's "x = 0 -> +0/-0" assertion is vacuous.  *)
let lemma_old_constraint_is_vacuous ()
  : Lemma (forall (z:zkind). old_constraint z)
  = ()

(* Reproduction of the reported bug: `result = nzero` together with    *)
(* the current constraint is SATISFIABLE, even though `ieee_ground_    *)
(* truth` is violated -- i.e. the current encoding admits an invalid    *)
(* model, exactly #7431's symptom. *)
let lemma_old_constraint_admits_invalid_model ()
  : Lemma (old_constraint NZero /\ ~(ieee_ground_truth NZero))
  = ()

(* ----------------------------------------------------------------- *)
(* The FIX: replace the disjunction with the single equation           *)
(* `result = pzero` (dropping the `nzero` disjunct unconditionally,     *)
(* for every rounding mode -- there is no mode-dependent case here,     *)
(* since the input `x = 0` carries no sign to round from).              *)
(* ----------------------------------------------------------------- *)

let new_constraint (z:zkind) : bool =
  (z = PZero)

(* The fix is sound: it only ever admits the ground-truth value. *)
let lemma_new_constraint_sound ()
  : Lemma (forall (z:zkind). new_constraint z ==> ieee_ground_truth z)
  = ()

(* The fix is strictly stronger than the current constraint: every     *)
(* `z` satisfying `new_constraint` also satisfies `old_constraint`,     *)
(* but not conversely (`NZero` is a counterexample to the converse).    *)
let lemma_new_constraint_stronger ()
  : Lemma ((forall (z:zkind). new_constraint z ==> old_constraint z) /\
           (old_constraint NZero /\ ~(new_constraint NZero)))
  = ()

(* The fix does not lose the genuine witness: `result = pzero` (the    *)
(* only IEEE-754-correct answer) remains satisfiable under it. *)
let lemma_new_constraint_complete ()
  : Lemma (new_constraint PZero)
  = ()

(* ----------------------------------------------------------------- *)
(* Capstone: the fix is exactly "replace `old_constraint` by `new_     *)
(* constraint`" -- i.e. `new_constraint` is the unique strengthening    *)
(* of `old_constraint` that both (a) is implied by, and implies,        *)
(* `ieee_ground_truth`, and (b) is satisfiable (nonempty). This          *)
(* confirms there is no weaker repair than "always +0": any predicate   *)
(* strictly between `new_constraint` and `old_constraint` on a two-      *)
(* element domain does not exist (there is no third `zkind` value       *)
(* to admit partially), so "x = 0 -> result = pzero" is the minimal,     *)
(* and only, correct fix.                                               *)
(* ----------------------------------------------------------------- *)

let lemma_fix_is_minimal_and_unique ()
  : Lemma (forall (p:zkind -> bool).
             (forall z. p z ==> old_constraint z) /\     // p refines old_constraint
             (forall z. p z ==> ieee_ground_truth z) /\   // p is sound w.r.t. ground truth
             (exists z. p z)                              // p is satisfiable
             ==> (forall z. p z <==> new_constraint z))
  = ()
