(*
   Z3PulseLraCheckerTests.fst

   Concrete-instance tests exercising `Z3LraFarkasTheory.fst`'s
   executable `farkas_decide` and `Z3PulseLraChecker.fst`'s Pulse
   mirror `check_farkas_decide` on real Farkas certificates: two
   harvested directly from genuine Z3 `PR_TH_LEMMA arith farkas`
   proof nodes (`polypaver-0047`, `sqrt-0108`, both produced with
   `smt.arith.solver=2` against QF_LRA SMT-LIB benchmarks -- see
   `LRA_FARKAS_REPORT.md` for the exact provenance/commands), plus two
   small hand-authored synthetic certificates covering a different
   combination shape (four antecedents cancelling a non-trivial
   positive constant, rather than three). All four are, by
   construction, genuinely infeasible combinations: `farkas_decide`
   must accept every one of them with the expected refuting constant.
   Two deliberately-malformed variants (one ill-formed per `wf_entry`,
   one well-formed but non-cancelling) confirm correct rejection.

   Every certificate here is represented directly as the *normalized*
   `cert_entry` list `check_arith_proof` would itself end up with
   after `check_arith_literal`'s own normalization step (see
   `normalize`'s docstring in `Z3LraFarkasTheory.fst`) -- i.e. this
   file is deliberately one layer "below" the raw SMT-LIB antecedent
   text, exactly where `farkas_decide`/`check_farkas_decide` operate;
   the raw-antecedent-to-`cert_entry` translation for each real
   benchmark is spelled out in the comment above each one so the
   correspondence to the actual proof-node text remains checkable by
   inspection.

   All coefficients/constants are plain integers, scaled up from the
   benchmarks' original rationals by a positive constant (which does
   not change validity -- see `Z3LraFarkasTheory.fst`'s header), the
   same all-integer representation `farkas_decide` itself uses
   throughout.
*)
module Z3PulseLraCheckerTests
#lang-pulse
open Pulse.Lib.Pervasives
open Z3LraFarkasTheory
open Z3PulseLraChecker
module L = FStar.List.Tot

(* ----------------------------------------------------------------- *)
(* Test 1: `polypaver-0047` -- three nonnegativity antecedents plus    *)
(* one combined upper bound, cancelling to a positive constant.        *)
(*                                                                     *)
(*   skoZ >= 0           (coeff 1)                                    *)
(*   skoX >= 0           (coeff 1)                                    *)
(*   skoY >= 0           (coeff 1)                                    *)
(*   skoZ+skoX+skoY <= -14/9   (coeff 1)                              *)
(*                                                                     *)
(* Normalized atoms (`normalize`'s `Ge`/`Le` branches, `is_pos=true`): *)
(*   -skoZ <= 0, -skoX <= 0, -skoY <= 0,                               *)
(*   9skoZ+9skoX+9skoY+14 <= 0   (the last clause scaled by 9 to       *)
(*   clear the denominator, coefficients 9/9/9/1 to compensate --      *)
(*   see the file header) *)
(* ----------------------------------------------------------------- *)

let pp_negZ : lin_term = { mono = [(-1, "skoZ")]; cst = 0 }
let pp_negX : lin_term = { mono = [(-1, "skoX")]; cst = 0 }
let pp_negY : lin_term = { mono = [(-1, "skoY")]; cst = 0 }
let pp_sum  : lin_term = { mono = [(9, "skoZ"); (9, "skoX"); (9, "skoY")]; cst = 14 }

let polypaver_cert : list cert_entry =
  [ { a = { term = pp_negZ; strict = false; is_eq = false }; c = 9 };
    { a = { term = pp_negX; strict = false; is_eq = false }; c = 9 };
    { a = { term = pp_negY; strict = false; is_eq = false }; c = 9 };
    { a = { term = pp_sum;  strict = false; is_eq = false }; c = 1 } ]

let lemma_polypaver_decide ()
  : Lemma (ensures farkas_decide polypaver_cert == Some 14)
  = ()

(* ----------------------------------------------------------------- *)
(* Test 2: `sqrt-0108` -- a strict lower bound combined with two       *)
(* upper-bound-shaped antecedents, cancelling to a positive constant.  *)
(*                                                                     *)
(*   skoX >= 1/20            (coeff 10)                                *)
(*   skoY <= 0               (coeff 1)                                *)
(*   10*skoX - skoY <= 0     (coeff 1)                                *)
(*                                                                     *)
(* Scaled by an overall factor of 20 (to clear `1/20`, as above);      *)
(* normalized atoms: `-20skoX+1 <= 0` (coeff 10), `skoY <= 0`          *)
(* (coeff 20), `10skoX-skoY <= 0` (coeff 20) -- cancelling to `10`      *)
(* (`= 20 * 1/2`, matching the un-scaled certificate's own constant). *)
(* ----------------------------------------------------------------- *)

let sq_lb  : lin_term = { mono = [(-20, "skoX")]; cst = 1 }
let sq_ub1 : lin_term = { mono = [(1, "skoY")]; cst = 0 }
let sq_ub2 : lin_term = { mono = [(10, "skoX"); (-1, "skoY")]; cst = 0 }

let sqrt_cert : list cert_entry =
  [ { a = { term = sq_lb;  strict = false; is_eq = false }; c = 10 };
    { a = { term = sq_ub1; strict = false; is_eq = false }; c = 20 };
    { a = { term = sq_ub2; strict = false; is_eq = false }; c = 20 } ]

let lemma_sqrt_decide ()
  : Lemma (ensures farkas_decide sqrt_cert == Some 10)
  = ()

(* ----------------------------------------------------------------- *)
(* Test 3: `synthetic2` -- a small three-antecedent hand-authored      *)
(* certificate.                                                       *)
(*                                                                     *)
(*   x >= 2          (coeff 2)                                        *)
(*   y >= 1          (coeff 3)                                        *)
(*   2x+3y <= 5      (coeff 1)                                        *)
(*                                                                     *)
(* Normalized atoms: `-x+2 <= 0` (coeff 2), `-y+1 <= 0` (coeff 3),      *)
(* `2x+3y-5 <= 0` (coeff 1) -- cancelling to `2`.                       *)
(* ----------------------------------------------------------------- *)

let s2_negx : lin_term = { mono = [(-1, "x")]; cst = 2 }
let s2_negy : lin_term = { mono = [(-1, "y")]; cst = 1 }
let s2_sum  : lin_term = { mono = [(2, "x"); (3, "y")]; cst = -5 }

let synthetic2_cert : list cert_entry =
  [ { a = { term = s2_negx; strict = false; is_eq = false }; c = 2 };
    { a = { term = s2_negy; strict = false; is_eq = false }; c = 3 };
    { a = { term = s2_sum;  strict = false; is_eq = false }; c = 1 } ]

let lemma_synthetic2_decide ()
  : Lemma (ensures farkas_decide synthetic2_cert == Some 2)
  = ()

(* ----------------------------------------------------------------- *)
(* Test 4: `synthetic1` -- a four-antecedent hand-authored certificate  *)
(* over three variables.                                              *)
(*                                                                     *)
(*   y+z <= 2        (coeff 1)                                        *)
(*   x+y+z >= 4      (coeff 2)                                        *)
(*   x+z <= 2        (coeff 1)                                        *)
(*   x+y <= 2        (coeff 1)                                        *)
(*                                                                     *)
(* Normalized atoms: `y+z-2 <= 0` (coeff 1),                            *)
(* `-x-y-z+4 <= 0` (coeff 2), `x+z-2 <= 0` (coeff 1),                   *)
(* `x+y-2 <= 0` (coeff 1) -- cancelling to `2`.                         *)
(* ----------------------------------------------------------------- *)

let s1_e1 : lin_term = { mono = [(1, "y"); (1, "z")]; cst = -2 }
let s1_e2 : lin_term = { mono = [(-1, "x"); (-1, "y"); (-1, "z")]; cst = 4 }
let s1_e3 : lin_term = { mono = [(1, "x"); (1, "z")]; cst = -2 }
let s1_e4 : lin_term = { mono = [(1, "x"); (1, "y")]; cst = -2 }

let synthetic1_cert : list cert_entry =
  [ { a = { term = s1_e1; strict = false; is_eq = false }; c = 1 };
    { a = { term = s1_e2; strict = false; is_eq = false }; c = 2 };
    { a = { term = s1_e3; strict = false; is_eq = false }; c = 1 };
    { a = { term = s1_e4; strict = false; is_eq = false }; c = 1 } ]

let lemma_synthetic1_decide ()
  : Lemma (ensures farkas_decide synthetic1_cert == Some 2)
  = ()

(* ----------------------------------------------------------------- *)
(* Rejection tests: ill-formed/non-cancelling certificates that        *)
(* `farkas_decide` must *not* accept.                                  *)
(* ----------------------------------------------------------------- *)

(* Not well-formed: `synthetic2`'s first entry's coefficient negated,
   a negative coefficient on a non-equality atom (`wf_entry` requires
   `e.a.is_eq \/ e.c >= 0`) -- `all_wf_b` must reject this before any
   folding happens at all. *)
let bad_wf_cert : list cert_entry =
  [ { a = { term = s2_negx; strict = false; is_eq = false }; c = -2 };
    { a = { term = s2_negy; strict = false; is_eq = false }; c = 3 };
    { a = { term = s2_sum;  strict = false; is_eq = false }; c = 1 } ]

let lemma_bad_wf_decide ()
  : Lemma (ensures farkas_decide bad_wf_cert == None)
  = ()

(* Well-formed, but missing `synthetic2`'s third entry entirely: the
   remaining two antecedents' variables do not cancel (`all_zero`
   fails), so there is no refuting constant to find. *)
let incomplete_cert : list cert_entry =
  [ { a = { term = s2_negx; strict = false; is_eq = false }; c = 2 };
    { a = { term = s2_negy; strict = false; is_eq = false }; c = 3 } ]

let lemma_incomplete_decide ()
  : Lemma (ensures farkas_decide incomplete_cert == None)
  = ()

(* ----------------------------------------------------------------- *)
(* Running the actual Pulse checker (`check_farkas_decide`) on every   *)
(* certificate above, confirming it returns exactly what `farkas_decide`
   itself computes -- i.e. that the genuinely imperative, step-counted
   Pulse code path (not just the pure specification) accepts/rejects
   each one correctly. *)
(* ----------------------------------------------------------------- *)

fn run_one (cert:list cert_entry) (expected:option int)
  requires pure (farkas_decide cert == expected)
  ensures emp
{
  let mut ctr = 0;
  let o = check_farkas_decide cert ctr;
  assert (pure (o == expected));
}

fn test_accepted_certificates ()
  requires emp
  ensures emp
{
  lemma_polypaver_decide ();
  run_one polypaver_cert (Some 14);
  lemma_sqrt_decide ();
  run_one sqrt_cert (Some 10);
  lemma_synthetic2_decide ();
  run_one synthetic2_cert (Some 2);
  lemma_synthetic1_decide ();
  run_one synthetic1_cert (Some 2);
}

fn test_rejected_certificates ()
  requires emp
  ensures emp
{
  lemma_bad_wf_decide ();
  run_one bad_wf_cert None;
  lemma_incomplete_decide ();
  run_one incomplete_cert None;
}

(* `farkas_accepts`'s boolean-only interface, exercised directly (pure,
   no Pulse/step-counter needed). *)
let lemma_farkas_accepts_true ()
  : Lemma (ensures farkas_accepts polypaver_cert == true /\
                   farkas_accepts sqrt_cert == true /\
                   farkas_accepts synthetic2_cert == true /\
                   farkas_accepts synthetic1_cert == true)
  = lemma_polypaver_decide ();
    lemma_sqrt_decide ();
    lemma_synthetic2_decide ();
    lemma_synthetic1_decide ()

let lemma_farkas_accepts_false ()
  : Lemma (ensures farkas_accepts bad_wf_cert == false /\
                   farkas_accepts incomplete_cert == false)
  = lemma_bad_wf_decide ();
    lemma_incomplete_decide ()

(* ----------------------------------------------------------------- *)
(* Finally, the end-to-end soundness corollary applied to each real/   *)
(* synthetic certificate: no environment `rho` can simultaneously      *)
(* satisfy all of a certificate's atoms once `farkas_decide` accepts   *)
(* it -- `lemma_check_farkas_decide_sound` (from                       *)
(* `Z3PulseLraChecker.fst`) already proves this in general; these      *)
(* four calls simply instantiate it concretely, confirming it applies  *)
(* to the genuine harvested certificates, not only to abstract ones.   *)
(* ----------------------------------------------------------------- *)

let lemma_polypaver_unsat (rho:var -> int)
  : Lemma (requires all_hold polypaver_cert rho) (ensures False)
  = lemma_farkas_decide_sound polypaver_cert rho

let lemma_sqrt_unsat (rho:var -> int)
  : Lemma (requires all_hold sqrt_cert rho) (ensures False)
  = lemma_farkas_decide_sound sqrt_cert rho

let lemma_synthetic2_unsat (rho:var -> int)
  : Lemma (requires all_hold synthetic2_cert rho) (ensures False)
  = lemma_farkas_decide_sound synthetic2_cert rho

let lemma_synthetic1_unsat (rho:var -> int)
  : Lemma (requires all_hold synthetic1_cert rho) (ensures False)
  = lemma_farkas_decide_sound synthetic1_cert rho
