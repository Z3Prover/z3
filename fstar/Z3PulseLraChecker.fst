(*
   Z3PulseLraChecker.fst

   A Pulse (genuinely imperative) executable checker for the LRA
   Farkas-certificate theory formalized in `Z3LraFarkasTheory.fst`,
   following the same "pure spec + Pulse `fn` mirroring it + corollary
   soundness lemma" pattern as `Z3PulseProofChecker.fst` and
   `Z3PulseJustificationChecker.fst` (see those files' own header
   comments for the general rationale: a step-counter `ref int`,
   threaded through every recursive call and incremented once per
   certificate entry processed, both exercises Pulse's genuinely
   imperative `ref`-mutation machinery and gives a precise,
   Pulse-proved cost bound -- `L.length cert` here, one step per
   antecedent -- for the decision procedure, matching
   `check_arith_proof`'s own single linear pass over its antecedents).

   Unlike the rewriter-calculus/justification checkers, this file does
   not need to re-decide any shape-dispatch logic of its own: all of
   the actual decision-making content (`fold_raw`'s per-entry
   well-formedness check, monomial-table collection, and the final
   `farkas_decide` zero/sign check) is *already* a plain, executable,
   recursive F* function in `Z3LraFarkasTheory.fst`, proved sound
   there (`lemma_farkas_decide_sound`). This file's job is narrower:
   show that a genuinely imperative, `ref`-mutating Pulse computation
   (as opposed to a purely functional one) computes exactly that
   already-proved-sound function -- i.e. that lifting the checker into
   an imperative shell (as any real implementation, including Z3's own
   C++ `check_arith_proof`, necessarily is) introduces no discrepancy
   from the pure specification.
*)
module Z3PulseLraChecker
#lang-pulse
open Pulse.Lib.Pervasives
open Z3LraFarkasTheory
module L = FStar.List.Tot

(* The imperative mirror of `fold_raw`: processes `cert` one entry at
   a time, incrementing `ctr` once per entry (so the total increase
   after the call is exactly `L.length cert`, every antecedent visited
   once, just as `check_arith_proof`'s own single `for` loop over its
   parameters does), and is Pulse-proved to return exactly what the
   pure `fold_raw` computes on the same inputs. *)
fn rec check_fold_raw (cert:list cert_entry) (tbl:list (int & var)) (k:int) (strict:bool) (ctr:ref int)
  requires pts_to ctr 'n
  returns r:fold_result
  ensures pts_to ctr ('n + L.length cert)
  ensures pure (r == fold_raw cert tbl k strict)
  decreases cert
{
  match cert {
    [] -> { { ftbl = tbl; fk = k; fstrict = strict } }
    e :: tl -> {
      let scaled = L.map (fun (c0, v) -> (e.c * c0, v)) e.a.term.mono;
      let tbl' = collect scaled tbl;
      let k' = k + e.c * e.a.term.cst;
      let strict' = strict || any_strict_b1 e;
      lemma_fold_raw_cons e tl tbl k strict;
      ctr := !ctr + 1;
      check_fold_raw tl tbl' k' strict' ctr
    }
  }
}

(* The imperative mirror of `farkas_decide`: the well-formedness gate
   is a single pass over `cert` (`all_wf_b`, already a plain
   non-Pulse, non-`ref`-touching recursive check, so it is called
   directly rather than re-threaded through the step counter -- only
   `check_fold_raw`'s per-entry accumulation is genuinely imperative
   here, matching the real checker's own structure: it validates each
   literal's shape, then separately accumulates the running symbolic
   sum). *)
fn check_farkas_decide (cert:list cert_entry) (ctr:ref int)
  requires pts_to ctr 'n
  returns ok:(option int)
  ensures pts_to ctr ('n + (if all_wf_b cert then L.length cert else 0))
  ensures pure (ok == farkas_decide cert)
{
  if (not (all_wf_b cert)) {
    None #int
  } else {
    let r = check_fold_raw cert [] 0 false ctr;
    if (all_zero r.ftbl && (if r.fstrict then r.fk >= 0 else r.fk > 0)) {
      Some r.fk
    } else {
      None #int
    }
  }
}

(* End-to-end corollary: running the Pulse checker and getting `Some`
   back is exactly as good a refutation witness as calling the pure
   `farkas_decide` directly -- i.e. composing `check_farkas_decide`'s
   Pulse-proved postcondition with `Z3LraFarkasTheory.fst`'s
   `lemma_farkas_decide_sound` gives: if the certificate's literals all
   actually hold under some valuation `rho`, the Pulse checker cannot
   have accepted it. *)
let lemma_check_farkas_decide_sound (cert:list cert_entry) (rho:var -> int) (ok:option int)
  : Lemma (requires ok == farkas_decide cert /\ Some? ok /\ all_hold cert rho)
          (ensures False)
  = lemma_farkas_decide_sound cert rho
