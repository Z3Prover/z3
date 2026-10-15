(*
   Z3PulseProofCheckerJson.fst

   The Pulse entry point for `Z3ProofJson.fst`'s verified, bottom-up
   JSON checker and the existing semantic soundness lemmas
   (`Z3PatternMatchedProofChecker.fst`'s `collect_unmatched`/matcher
   library). This is the one module every
   per-proof "instance" file (see `tools/extract_z3_proof.py`'s
   `--json` mode) actually calls; it, together with every module it
   depends on, is compiled and `.checked`-cached *once* -- a new proof
   never requires recompiling anything in this file or below it, only
   re-elaborating a tiny instance file that supplies a new JSON
   *string* and invokes the functions below on it.

   `run_proof_json`/`check_proof_json` are the imperative (Pulse)
   counterpart of `Z3ProofJson.fst`'s pure `check_proof_json_wf`; they
   consume a cached result proved equal to `fact` of the decoded proof,
   rather than revisiting shared subproofs with a recursive traversal.
   Thus
   (combined with `lemma_proof_json_sound`/`lemma_proof_json_cross_
   checked` below) a caller gets the same end-to-end guarantee the old
   per-proof `.fst`-generation path gave (`lemma_extracted_proof_
   wellformed` + `lemma_unmatched_count_cross_checked` +
   `check_extracted`), without needing a bespoke module per proof.
*)
module Z3PulseProofCheckerJson
#lang-pulse
open Pulse.Lib.Pervasives
open Z3AstTheory
open Z3ProofTheory
open Z3ProofJson
open Z3ValueTheory
open Z3PulseProofChecker
open Z3InterpretedProofChecker
open Z3PatternMatchedProofChecker

(* ----------------------------------------------------------------- *)
(* 1. Pure corollaries: what a successful parse + check means          *)
(* ----------------------------------------------------------------- *)

(* If `s` parses to a document whose root proof `p` is well-formed
   (`fact p = Some (a, b)`) and every `Rewrite` leaf of `p` is matched
   by this project's verified rewrite-rule library
   (`all_matched p`, `Z3PatternMatchedProofChecker.fst`), then `a` and
   `b` are semantically equal under *every* environment -- the same
   "fully proved, no leftover trust" guarantee the old `all_matched`
   path gave for a literal, hand-`.fst`-encoded proof, now established
   for a proof that arrived as a JSON string. *)
let lemma_proof_json_sound (s:string) (rho:env value)
  : Lemma (requires (match parse_proof_doc s with
                      | Some (p, _) -> Some? (fact p) /\ all_matched p
                      | None -> False))
          (ensures (let Some (p, _) = parse_proof_doc s in
                    let Some (a, b) = fact p in
                    eval the_interpretation a rho == eval the_interpretation b rho))
  = let Some (p, _) = parse_proof_doc s in
    lemma_matched_proof_true p rho

(* The weaker, "partial" counterpart: soundness given only that the
   document's *unmatched* leaves (exactly `collect_unmatched p`, the
   same leftover-obligations list `Z3PatternMatchedProofChecker.fst`'s
   "partial mode" already defines) are semantically sound, however
   that is established. *)
let lemma_proof_json_partial_sound (s:string) (rho:env value)
  : Lemma (requires (match parse_proof_doc s with
                      | Some (p, _) -> Some? (fact p) /\ leftover_sound (collect_unmatched p)
                      | None -> False))
          (ensures (let Some (p, _) = parse_proof_doc s in
                    let Some (a, b) = fact p in
                    eval the_interpretation a rho == eval the_interpretation b rho))
  = let Some (p, _) = parse_proof_doc s in
    lemma_partial_proof_true p rho

(* Cross-check corollary, mirroring the old per-proof `.fst` template's
   `lemma_unmatched_count_cross_checked`: if `s` parses, its document's
   own declared `unmatched_count` annotation agrees with
   `collect_unmatched`'s real, freshly recomputed count -- i.e. the
   harness's bookkeeping (whatever produced the JSON) was not out of
   sync with the verified matcher library at the time it was written. *)
let proof_json_unmatched_count_matches (s:string) : bool =
  match parse_proof_doc s with
  | Some (p, n) -> FStar.List.Tot.length (collect_unmatched p) = n
  | None -> false

(* ----------------------------------------------------------------- *)
(* 2. The Pulse entry point                                             *)
(* ----------------------------------------------------------------- *)

(* Parses and checks `s` bottom-up, once per proof-array entry. Cached
   successes and failures have the refinement `result == fact term`;
   using a shared premise never traverses that premise again.
   Returns `None` if `s` does not even parse/decode to a well-formed
   proof, `Some (Some? (fact p))` otherwise -- i.e. "did this string
   describe a proof at all" is distinguished from "was that proof
   well-formed". *)
fn run_proof_json (s:string)
  requires emp
  returns ok:(option bool)
  ensures pure (ok == (match parse_proof_doc s with
                       | Some (p, _) -> Some (Some? (fact p))
                       | None -> None))
{
  match parse_checked_proof_doc s {
    Some pr -> {
      let p = fst pr;
      let o = p.result;
      match o {
        Some _ -> { Some true }
        None -> { Some false }
      }
    }
    None -> { None }
  }
}

(* Self-contained boolean convenience wrapper: `true` iff `s` parses to
   a well-formed proof document whose root proof is well-formed. This
   is the function a tiny per-proof instance file's
   `assert_norm`/F*-normalizer call is expected to invoke (see
   `tools/extract_z3_proof.py`'s `--json` output). *)
fn check_proof_json (s:string)
  requires emp
  returns ok:bool
  ensures pure (ok == (match parse_proof_doc s with
                       | Some (p, _) -> Some? (fact p)
                       | None -> false))
{
  let r = run_proof_json s;
  match r {
    Some b -> { b }
    None -> { false }
  }
}
