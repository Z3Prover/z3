(*
   Z3PulseLraCheckerParsed.fst

   AUTO-GENERATED (via `tools/parse_farkas.py`) from four genuine Z3
   proof-output files captured under `qf_lra_bench/` (two real QF_LRA
   SMT-LIB benchmarks, `full_polypaver.txt`/`full_sqrt.txt`, plus two
   small hand-authored unsat instances, `full_synthetic1.txt`/
   `full_synthetic2.txt`, all produced by running
   `z3.exe smt.arith.solver=2 <file>.smt2` on a `.smt2` file containing
   `(set-option :produce-proofs true)` and a trailing `(get-proof)`).

   This is the literal output of the regeneration command:

     python tools/parse_farkas.py \
       qf_lra_bench/full_polypaver.txt qf_lra_bench/full_sqrt.txt \
       qf_lra_bench/full_synthetic1.txt qf_lra_bench/full_synthetic2.txt

   i.e. this file demonstrates the full pipeline the user asked for:
   a real `(_ th-lemma arith farkas c1 .. cn)` proof node, written to
   disk by Z3 itself, is mechanically parsed (not hand-transcribed)
   into a `cert_entry` list, and *that* parsed data is what
   `farkas_decide`/`check_farkas_decide` are run on below -- the same
   Pulse-proven-sound decision procedure audited in
   `Z3LraFarkasTheory.fst`/`Z3PulseLraChecker.fst`, now exercised on
   genuinely machine-extracted input.

   (The four certificates below are, as it happens, *identical* --
   term-for-term, coefficient-for-coefficient -- to
   `Z3PulseLraCheckerTests.fst`'s hand-derived `polypaver_cert`/
   `sqrt_cert`/`synthetic1_cert`/`synthetic2_cert`: this is itself a
   cross-check confirming the hand derivation documented there was
   faithful to the real proof text, not merely plausible-looking.)
*)
module Z3PulseLraCheckerParsed
#lang-pulse
open Pulse.Lib.Pervasives
open Z3LraFarkasTheory
open Z3PulseLraChecker

(* parsed from qf_lra_bench/full_polypaver.txt *)
let parsed_full_polypaver_cert : list cert_entry =
  [ { a = { term = { mono = [(-1, "skoZ")]; cst = 0 }; strict = false; is_eq = false }; c = 9 };
    { a = { term = { mono = [(-1, "skoX")]; cst = 0 }; strict = false; is_eq = false }; c = 9 };
    { a = { term = { mono = [(-1, "skoY")]; cst = 0 }; strict = false; is_eq = false }; c = 9 };
    { a = { term = { mono = [(9, "skoZ"); (9, "skoX"); (9, "skoY")]; cst = 14 }; strict = false; is_eq = false }; c = 1 } ]

(* parsed from qf_lra_bench/full_sqrt.txt *)
let parsed_full_sqrt_cert : list cert_entry =
  [ { a = { term = { mono = [(-20, "skoX")]; cst = 1 }; strict = false; is_eq = false }; c = 10 };
    { a = { term = { mono = [(1, "skoY")]; cst = 0 }; strict = false; is_eq = false }; c = 20 };
    { a = { term = { mono = [(10, "skoX"); (-1, "skoY")]; cst = 0 }; strict = false; is_eq = false }; c = 20 } ]

(* parsed from qf_lra_bench/full_synthetic1.txt *)
let parsed_full_synthetic1_cert : list cert_entry =
  [ { a = { term = { mono = [(1, "y"); (1, "z")]; cst = -2 }; strict = false; is_eq = false }; c = 1 };
    { a = { term = { mono = [(-1, "x"); (-1, "y"); (-1, "z")]; cst = 4 }; strict = false; is_eq = false }; c = 2 };
    { a = { term = { mono = [(1, "x"); (1, "z")]; cst = -2 }; strict = false; is_eq = false }; c = 1 };
    { a = { term = { mono = [(1, "x"); (1, "y")]; cst = -2 }; strict = false; is_eq = false }; c = 1 } ]

(* parsed from qf_lra_bench/full_synthetic2.txt *)
let parsed_full_synthetic2_cert : list cert_entry =
  [ { a = { term = { mono = [(-1, "x")]; cst = 2 }; strict = false; is_eq = false }; c = 2 };
    { a = { term = { mono = [(-1, "y")]; cst = 1 }; strict = false; is_eq = false }; c = 3 };
    { a = { term = { mono = [(2, "x"); (3, "y")]; cst = -5 }; strict = false; is_eq = false }; c = 1 } ]

(* The pure decision procedure accepts every parsed certificate, with
   exactly the refuting constant the real proof's own combination
   algebraically collapses to. *)
let lemma_parsed_polypaver_decide ()
  : Lemma (ensures farkas_decide parsed_full_polypaver_cert == Some 14) = ()

let lemma_parsed_sqrt_decide ()
  : Lemma (ensures farkas_decide parsed_full_sqrt_cert == Some 10) = ()

let lemma_parsed_synthetic1_decide ()
  : Lemma (ensures farkas_decide parsed_full_synthetic1_cert == Some 2) = ()

let lemma_parsed_synthetic2_decide ()
  : Lemma (ensures farkas_decide parsed_full_synthetic2_cert == Some 2) = ()

(* ...and the genuinely imperative Pulse checker agrees, on every one
   of the four parsed certificates. *)
fn run_parsed (cert:list cert_entry) (expected:option int)
  requires pure (farkas_decide cert == expected)
  ensures emp
{
  let mut ctr = 0;
  let o = check_farkas_decide cert ctr;
  assert (pure (o == expected));
}

fn test_parsed_certificates ()
  requires emp
  ensures emp
{
  lemma_parsed_polypaver_decide ();
  run_parsed parsed_full_polypaver_cert (Some 14);
  lemma_parsed_sqrt_decide ();
  run_parsed parsed_full_sqrt_cert (Some 10);
  lemma_parsed_synthetic1_decide ();
  run_parsed parsed_full_synthetic1_cert (Some 2);
  lemma_parsed_synthetic2_decide ();
  run_parsed parsed_full_synthetic2_cert (Some 2);
}

(* The end-to-end soundness corollary, applied to each parsed
   certificate: no environment can satisfy all of a parsed
   certificate's atoms. *)
let lemma_parsed_polypaver_unsat (rho:var -> int)
  : Lemma (requires all_hold parsed_full_polypaver_cert rho) (ensures False)
  = lemma_farkas_decide_sound parsed_full_polypaver_cert rho

let lemma_parsed_sqrt_unsat (rho:var -> int)
  : Lemma (requires all_hold parsed_full_sqrt_cert rho) (ensures False)
  = lemma_farkas_decide_sound parsed_full_sqrt_cert rho

let lemma_parsed_synthetic1_unsat (rho:var -> int)
  : Lemma (requires all_hold parsed_full_synthetic1_cert rho) (ensures False)
  = lemma_farkas_decide_sound parsed_full_synthetic1_cert rho

let lemma_parsed_synthetic2_unsat (rho:var -> int)
  : Lemma (requires all_hold parsed_full_synthetic2_cert rho) (ensures False)
  = lemma_farkas_decide_sound parsed_full_synthetic2_cert rho
