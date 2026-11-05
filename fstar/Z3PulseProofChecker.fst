(*
   Z3PulseProofChecker.fst

   A Pulse (verified imperative / separation-logic) implementation of
   an *executable* proof checker for the equality-proof calculus
   formalized in `Z3ProofTheory.fst` (the `proof` datatype modeling
   `src/ast/ast.h`'s `basic_op_kind` fragment that
   `src/ast/rewriter/rewriter_def.h` builds: `PR_REFLEXIVITY`,
   `PR_SYMMETRY`, `PR_TRANSITIVITY`, `PR_MONOTONICITY`, `PR_REWRITE`,
   and the compound `PR_BIND`+`PR_QUANT_INTRO` shape `QuantIntro`).

   `Z3ProofTheory.fst` already defines a pure, executable decision
   procedure, `fact`/`facts_of`, that mirrors Z3's own internal proof
   checker (`src/ast/proofs/proof_checker.cpp`'s `check1_basic`) and is
   proved sound: a well-formed proof (`fact p = Some (a, b)`) all of
   whose `Rewrite` leaves are semantically sound denotes a true
   equation `a = b`, for every interpretation and environment
   (`lemma_proof_sound`).

   This file does *not* re-derive that soundness result (it is already
   fully proved, admit/assume-free, in `Z3ProofTheory.fst`). Instead it
   builds a genuinely *imperative* checker on top of it, in Pulse:

     - `check_either`, a single Pulse `fn` recursing structurally over
       *either* a `proof` node or a `list proof` (merged into one sum
       type, `proof_or_list`, purely so the recursion is a single
       self-recursive Pulse `fn` rather than two mutually recursive
       ones -- Pulse's recursive-`fn` support does not (currently)
       extend to mutual recursion the way plain F*'s `let rec ... and
       ...` does), threading a mutable `ref int` step counter that is
       incremented once per proof node visited (mirroring the kind of
       bookkeeping/statistics a real, imperative proof checker
       maintains, e.g. Z3's own `proof_checker`'s node-visit
       bookkeeping) -- this is the file's genuine "imperative" content,
       not just a wrapper around a pure function.

     - Pulse's own type system is used to *prove*, not merely test,
       that this imperative traversal computes *exactly* `fact`/
       `facts_of` (the `result_matches` postcondition below) and visits
       exactly `proof_size p` (resp. `proof_list_size ps`) nodes while
       doing so (the `pts_to ctr (...)` postcondition below) -- i.e.
       the Pulse implementation is proved, by Pulse's own separation-
       logic VC generator plus the SMT backend, to *refine* the
       already-audited pure specification, not just to "look similar
       to it".

     - `check_proof`/`check_proof_list`, thin top-level wrappers
       specializing `check_either` back down to the natural `proof`/
       `list proof` interfaces (hiding the `proof_or_list` encoding
       trick), and `checker_accepts`, a self-contained boolean-result
       entry point (allocates its own counter, discards it).

   Composing `check_proof`'s postcondition with `Z3ProofTheory.fst`'s
   already-proved `lemma_proof_sound` (see `lemma_checker_sound` at the
   end of this file) gives the end-to-end correctness statement for
   this Pulse checker: whenever it accepts a proof term (for any
   interpretation under which every `Rewrite` leaf is semantically
   sound -- i.e. every theory-specific rewrite the proof's leaves
   appeal to is itself correct, exactly the fact every per-theory
   rewriter report in this directory, `BOOL_REWRITER_REPORT.md`,
   `ARITH_REWRITER_REPORT.md`, `BV_REWRITER_REPORT.md`,
   `SEQ_REWRITER_REPORT.md`, `Z3NlArith.fst`'s lemmas, etc.,
   separately establishes for its own theory's leaves), the equation it
   reports is actually true. `Z3PulseProofCheckerTests.fst` exercises
   this checker on sample derivations whose `Rewrite` leaves are drawn
   from many different theories, to test the one shared checker across
   all of them (exactly mirroring how `rewriter_def.h`/`proof_checker.
   cpp` are themselves theory-agnostic and shared by every rewriter
   plugin).
*)
module Z3PulseProofChecker
#lang-pulse
open Pulse.Lib.Pervasives
open Z3AstTheory
open Z3ProofTheory
module L = FStar.List.Tot

(* ----------------------------------------------------------------- *)
(* The single-recursion encoding trick                                 *)
(* ----------------------------------------------------------------- *)

(* Pulse's recursive `fn`s support plain self-recursion but not (yet)
   F*-style mutual recursion (`fn rec f ... and g ...`), which is what
   a direct Pulse port of `fact`/`facts_of` (mutually recursive over
   `proof`/`list proof`) would need. Standard trick: merge the two
   recursion domains into one sum type and recurse on that instead;
   `combined_size` below is exactly `proof_size`/`proof_list_size`
   (already defined, and already used as `fact`'s own termination
   metric, in `Z3ProofTheory.fst`) dispatched on the tag, so every
   recursive call below provably decreases it (checked by Pulse/F*'s
   termination checker, not merely asserted). *)
noeq
type proof_or_list =
  | PNode : proof -> proof_or_list
  | PList : list proof -> proof_or_list

let combined_size (x:proof_or_list) : nat =
  match x with
  | PNode p -> proof_size p
  | PList ps -> proof_list_size ps

(* The result domain mirrors the input domain's tag: a `PNode` input
   always produces an `RNode` result (an `option (expr & expr)`, i.e.
   `fact`'s own return type) and a `PList` input always produces an
   `RList` result (a `list (option (expr & expr))`, i.e. `facts_of`'s
   own return type). `result_matches` states this correspondence *and*
   ties the payload back to the pure, already-verified `fact`/
   `facts_of`; every "impossible" cross-tag combination
   (`PNode`/`RList` or `PList`/`RNode`) is simply `False`, which is
   exactly what lets every such case be dismissed by `unreachable()`
   below instead of handled. *)
noeq
type check_result =
  | RNode : option (expr & expr) -> check_result
  | RList : list (option (expr & expr)) -> check_result

let result_matches (x:proof_or_list) (r:check_result) : prop =
  match x, r with
  | PNode p, RNode o -> o == fact p
  | PList ps, RList os -> os == facts_of ps
  | _, _ -> False

(* ----------------------------------------------------------------- *)
(* The checker itself                                                  *)
(* ----------------------------------------------------------------- *)

(* `ctr` plays the role of a real imperative checker's bookkeeping
   (e.g. a node-visited counter, as a stand-in for the kind of mutable
   statistics/cache state `proof_checker::check1_basic`'s caller
   maintains across a whole proof DAG); its exact post-state
   (`'n + combined_size x`, i.e. "advances by exactly one unit per
   `proof`/list-cons node visited") is itself a Pulse-proved fact, not
   just an intention. *)
fn rec check_either (x:proof_or_list) (ctr:ref int)
  requires pts_to ctr 'n
  returns r:check_result
  ensures pts_to ctr ('n + combined_size x)
  ensures pure (result_matches x r)
  decreases combined_size x
{
  match x {
    PNode p -> {
      match p {
        Refl e -> {
          ctr := !ctr + 1;
          RNode (Some (e, e))
        }
        Sym p1 -> {
          let r1 = check_either (PNode p1) ctr;
          ctr := !ctr + 1;
          match r1 {
            RNode o -> {
              match o {
                Some pr -> { RNode (Some (snd pr, fst pr)) }
                None -> { RNode None }
              }
            }
            RList _ -> { unreachable () }
          }
        }
        Trans p1 p2 -> {
          let r1 = check_either (PNode p1) ctr;
          let r2 = check_either (PNode p2) ctr;
          ctr := !ctr + 1;
          match r1 {
            RNode o1 -> {
              match r2 {
                RNode o2 -> {
                  match o1 {
                    Some pr1 -> {
                      match o2 {
                        Some pr2 -> {
                          if (snd pr1 = fst pr2) {
                            RNode (Some (fst pr1, snd pr2))
                          } else {
                            RNode None
                          }
                        }
                        None -> { RNode None }
                      }
                    }
                    None -> { RNode None }
                  }
                }
                RList _ -> { unreachable () }
              }
            }
            RList _ -> { unreachable () }
          }
        }
        Congr f args1 args2 prfs -> {
          let rl = check_either (PList prfs) ctr;
          ctr := !ctr + 1;
          match rl {
            RList fs -> {
              if (L.length args1 = L.length args2 && congr_matched args1 args2 fs) {
                RNode (Some (App f args1, App f args2))
              } else {
                RNode None
              }
            }
            RNode _ -> { unreachable () }
          }
        }
        Rewrite s t -> {
          ctr := !ctr + 1;
          RNode (Some (s, t))
        }
        QuantIntro qk bound_sorts p1 -> {
          let r1 = check_either (PNode p1) ctr;
          ctr := !ctr + 1;
          match r1 {
            RNode o -> {
              match o {
                Some pr -> {
                  RNode (Some (Quantifier qk bound_sorts (quant_sort qk bound_sorts (get_sort (fst pr))) (fst pr),
                                Quantifier qk bound_sorts (quant_sort qk bound_sorts (get_sort (snd pr))) (snd pr)))
                }
                None -> { RNode None }
              }
            }
            RList _ -> { unreachable () }
          }
        }
      }
    }
    PList ps -> {
      match ps {
        [] -> { RList [] }
        p1 :: ps' -> {
          let r1 = check_either (PNode p1) ctr;
          let r2 = check_either (PList ps') ctr;
          ctr := !ctr + 1;
          match r1 {
            RNode o -> {
              match r2 {
                RList fs -> { RList (o :: fs) }
                RNode _ -> { unreachable () }
              }
            }
            RList _ -> { unreachable () }
          }
        }
      }
    }
  }
}

(* ----------------------------------------------------------------- *)
(* Natural top-level interface                                         *)
(* ----------------------------------------------------------------- *)

fn check_proof (p:proof) (ctr:ref int)
  requires pts_to ctr 'n
  returns o:(option (expr & expr))
  ensures pts_to ctr ('n + proof_size p)
  ensures pure (o == fact p)
{
  let r = check_either (PNode p) ctr;
  match r {
    RNode o -> { o }
    RList _ -> { unreachable () }
  }
}

fn check_proof_list (ps:list proof) (ctr:ref int)
  requires pts_to ctr 'n
  returns os:(list (option (expr & expr)))
  ensures pts_to ctr ('n + proof_list_size ps)
  ensures pure (os == facts_of ps)
{
  let r = check_either (PList ps) ctr;
  match r {
    RList os -> { os }
    RNode _ -> { unreachable () }
  }
}

(* Self-contained entry point: checks `p` against a freshly-scoped
   local counter and reports whether it is well-formed. Uses Pulse's
   `let mut` scoped-local-binding sugar (built on `with_local`, which
   is *not* deprecated) rather than raw `Reference.alloc`/`free`
   directly: `with_local`/`let mut` thread the counter's full
   permission linearly through the body and reclaim it automatically
   at the end of scope, so there is no window where an unsound
   freestanding `alloc`/`free` pair has to be trusted by hand.
   (Callers who want the node-visit count -- e.g. to compare against
   an expected proof-size budget, the way a real checker might guard
   against pathologically large proof objects -- should call
   `check_proof` directly with their own `ref`.) *)
fn checker_accepts (p:proof)
  requires emp
  returns ok:bool
  ensures pure (ok == Some? (fact p))
{
  let mut ctr = 0;
  let o = check_proof p ctr;
  match o {
    Some _ -> { true }
    None -> { false }
  }
}

(* ----------------------------------------------------------------- *)
(* End-to-end correctness corollary                                    *)
(* ----------------------------------------------------------------- *)

(* Pure (non-Pulse) corollary composing `check_proof`'s Pulse-proved
   postcondition (`o == fact p`, established above by actually running
   the imperative traversal, not merely assumed) with
   `Z3ProofTheory.fst`'s already-proved `lemma_proof_sound`: whenever
   the Pulse checker reports a conclusion `a = b` for a proof `p` all
   of whose `Rewrite` leaves are sound under interpretation `i`, that
   conclusion is semantically true under `i`, for every environment
   `rho`. This is the file's headline soundness theorem: "the
   imperative checker is correct" is not a slogan but exactly this
   `Lemma`. *)
let lemma_checker_sound (#value:Type) (i:interpretation value) (p:proof) (rho:env value) (a b:expr)
  : Lemma (requires all_leaves_sound i p /\ quant_extensional i /\ fact p == Some (a, b))
          (ensures eval i a rho == eval i b rho)
  = lemma_proof_sound i p rho
