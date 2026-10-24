(*
   Z3PulseJustificationChecker.fst

   A second Pulse checker, complementing `Z3PulseProofChecker.fst`'s
   rewriter-calculus checker, for the other proof-combinator layer
   formalized in this directory: `Z3ProofJustifications.fst`'s
   `PR_MODUS_PONENS` and `PR_UNIT_RESOLUTION`, the two proof
   combinators `src/smt/smt_justification.cpp` uses to build the SMT
   core's conflict-resolution proofs (see that file's own header
   comment for the detailed Z3 source correspondence).

   Unlike `Z3ProofTheory.fst`'s `proof`/`fact`, `Z3ProofJustifications.
   fst` does not define a single recursive proof-tree checker: modus
   ponens and unit resolution are each *flat*, single-step inference
   rules (combine already-established facts into a new one), stated
   there as a family of per-shape soundness lemmas
   (`lemma_mp_implies_sound`/`lemma_mp_eq_sound`/`lemma_mp_oeq_sound`,
   `lemma_resolve_residual_sound`/`lemma_unit_resolution_singleton_
   sound`) rather than as one executable decision procedure. This file
   adds that missing executable layer -- in Pulse -- and proves each
   decision procedure exactly decides what its corresponding lemma
   assumes, so accepting implies sound.
*)
module Z3PulseJustificationChecker
#lang-pulse
open Pulse.Lib.Pervasives
open Z3AstTheory
open Z3ProofJustifications
module L = FStar.List.Tot

(* ----------------------------------------------------------------- *)
(* `PR_MODUS_PONENS` / `PR_MODUS_PONENS_OEQ`                            *)
(* ----------------------------------------------------------------- *)

(* `ast_manager::mk_modus_ponens`'s own shape-dispatch order
   (implies, then `=`, then `~`/oeq), reusing the recognizers already
   defined (and used by the corresponding soundness lemmas) in
   `Z3ProofJustifications.fst` rather than re-deciding the same shapes
   by hand. *)
let decide_mp (f1 f2:expr) : option expr =
  match is_implies f2 with
  | Some pr -> if f1 = fst pr then Some (snd pr) else None
  | None ->
    (match is_eq_e f2 with
     | Some pr -> if f1 = fst pr then Some (snd pr) else None
     | None ->
       (match is_oeq_e f2 with
        | Some pr -> if f1 = fst pr then Some (snd pr) else None
        | None -> None))

(* `decide_mp` only ever accepts exactly the shapes the three
   `lemma_mp_*_sound` lemmas separately cover, so composing them
   recovers the single theorem: whenever `decide_mp` accepts, the
   conclusion it reports is semantically justified from `f1`/`f2`
   alone (for *every* atom valuation `v`, i.e. regardless of which
   theory's atoms `f1`/`f2`/the result mention -- modus ponens is a
   purely propositional rule, exactly `Z3ProofJustifications.fst`'s
   own header comment explains). *)
let lemma_decide_mp_sound (v:expr -> bool) (f1 f2:expr)
  : Lemma (requires Some? (decide_mp f1 f2) /\ blit_eval v f1 /\ blit_eval v f2)
          (ensures blit_eval v (Some?.v (decide_mp f1 f2)))
  = match is_implies f2 with
    | Some pr -> lemma_mp_implies_sound v f1 f2 (fst pr) (snd pr)
    | None ->
      (match is_eq_e f2 with
       | Some pr -> lemma_mp_eq_sound v f1 f2 (fst pr) (snd pr)
       | None ->
         (match is_oeq_e f2 with
          | Some pr -> lemma_mp_oeq_sound v f1 f2 (fst pr) (snd pr)
          | None -> ()))

(* The Pulse entry point: a thin imperative shell around `decide_mp`,
   threading a step counter (incremented once per call, mirroring
   `check_either`'s per-node bookkeeping in `Z3PulseProofChecker.fst`)
   and Pulse-proving the shell computes exactly `decide_mp`. *)
fn check_modus_ponens (f1 f2:expr) (ctr:ref int)
  requires pts_to ctr 'n
  returns ot:(option expr)
  ensures pts_to ctr ('n + 1)
  ensures pure (ot == decide_mp f1 f2)
{
  ctr := !ctr + 1;
  decide_mp f1 f2
}

(* ----------------------------------------------------------------- *)
(* `PR_UNIT_RESOLUTION`                                                 *)
(* ----------------------------------------------------------------- *)

(* Ported, as genuine Pulse recursion (no mutual-recursion encoding
   trick needed here: unlike `Z3ProofTheory.fst`'s `fact`/`facts_of`,
   `has_complement`'s recursion over `negs` never calls back into a
   sibling list-of-proofs checker), from `Z3ProofJustifications.fst`'s
   `has_complement`. Does not short-circuit on an early match (unlike
   the pure `||`-based original) so that the step counter's increase
   has the simple closed form `L.length negs`, visiting every
   candidate complement once. *)
fn rec check_has_complement (lit:expr) (negs:list expr) (ctr:ref int)
  requires pts_to ctr 'n
  returns b:bool
  ensures pts_to ctr ('n + L.length negs)
  ensures pure (b == has_complement lit negs)
  decreases negs
{
  match negs {
    [] -> { false }
    n :: negs' -> {
      let b1 = is_complement lit n;
      let b2 = check_has_complement lit negs' ctr;
      ctr := !ctr + 1;
      (b1 || b2)
    }
  }
}

(* `resolve_residual`'s cost, as a function of both list lengths, used
   only to state `check_resolve_residual`'s step-counter postcondition
   precisely (every clause literal is checked against every supplied
   complement-candidate once). *)
let rec resolve_residual_cost (lits negs:list expr) : nat =
  match lits with
  | [] -> 0
  | _ :: lits' -> 1 + L.length negs + resolve_residual_cost lits' negs

fn rec check_resolve_residual (lits:list expr) (negs:list expr) (ctr:ref int)
  requires pts_to ctr 'n
  returns out:(list expr)
  ensures pts_to ctr ('n + resolve_residual_cost lits negs)
  ensures pure (out == resolve_residual lits negs)
  decreases lits
{
  match lits {
    [] -> { [] }
    l :: lits' -> {
      let b = check_has_complement l negs ctr;
      ctr := !ctr + 1;
      if b {
        check_resolve_residual lits' negs ctr
      } else {
        let rest = check_resolve_residual lits' negs ctr;
        l :: rest
      }
    }
  }
}

(* End-to-end soundness corollary for unit resolution's main branch:
   composing `check_resolve_residual`'s Pulse-proved postcondition
   (`out == resolve_residual lits negs`) with `Z3ProofJustifications.
   fst`'s already-proved `lemma_resolve_residual_sound` gives "if the
   Pulse-checked clause `lits` holds and every supplied complement
   antecedent in `negs` holds, the reported residual clause `out`
   holds", for every atom valuation. *)
let lemma_check_resolve_residual_sound (v:expr -> bool) (lits negs:list expr)
  : Lemma (requires bclause_eval v lits /\ (forall n. L.memP n negs ==> blit_eval v n))
          (ensures bclause_eval v (resolve_residual lits negs))
  = lemma_resolve_residual_sound v lits negs

(* The degenerate two-premise branch (`f1` not itself a clause):
   `check_has_complement` at `negs = [f2]` already decides it (`b ==
   is_complement f1 f2 || false == is_complement f1 f2`), and
   `lemma_unit_resolution_singleton_sound` is the corresponding
   soundness statement (both `f1` and its complement `f2` holding is
   contradictory), reused unchanged. *)
let lemma_check_singleton_sound (v:expr -> bool) (f1 f2:expr)
  : Lemma (requires is_complement f1 f2 /\ blit_eval v f1 /\ blit_eval v f2)
          (ensures False)
  = lemma_unit_resolution_singleton_sound v f1 f2
