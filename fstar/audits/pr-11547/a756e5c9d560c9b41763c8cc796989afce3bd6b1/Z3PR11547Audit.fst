module Z3PR11547Audit
(* Abstract model of three PR #11547 changes. Fact of a proof is a formula id;
   0 stands for `false`. *)
type fact = nat
type proof = option fact   (* None = null proof pointer; Some f = proof with get_fact = f *)

type outcome = | Throw | AssertFalse : proof -> outcome

(* smt_tactic_core.cpp, case l_false (head): throws when proofs enabled and
   pr is null or its fact is not false; otherwise asserts false with pr. *)
let smt_false (proofs:bool) (pr:proof) : outcome =
  if proofs && (match pr with None -> true | Some f -> f <> 0) then Throw
  else AssertFalse pr

(* O1: no fabricated proof: any non-throwing result under proofs carries the solver proof of false *)
let o1 (pr:proof)
  : Lemma (match smt_false true pr with
           | Throw -> True
           | AssertFalse p -> p == pr /\ p == Some 0)
  = ()

(* O1b: with proofs disabled the pr is passed through unchanged (no new throw) *)
let o1b (pr:proof) : Lemma (smt_false false pr == AssertFalse pr) = ()

(* then_simplifier::reduce skip rule. Simplifier = supports flag + step on a state. *)
noeq type simp (s:Type) = { supports: bool; step: s -> s }
let run_one (#s:Type) (proofs:bool) (x:simp s) (st:s) : s =
  if proofs && not x.supports then st else x.step st
let rec run (#s:Type) (proofs:bool) (l:list (simp s)) (st:s) : s =
  match l with [] -> st | x::tl -> run proofs tl (run_one proofs x st)

(* O2: with proofs enabled, state is changed only by proof-supporting simplifiers *)
let o2 (#s:Type) (x:simp s) (st:s)
  : Lemma (requires not x.supports) (ensures run_one true x st == st) = ()
(* O2b: with proofs disabled behaviour equals old behaviour *)
let o2b (#s:Type) (x:simp s) (st:s) : Lemma (run_one false x st == x.step st) = ()

(* Tactic bypass (e.g. horn_tactic, eq2bv): proofs on => result is the input goal. *)
type goal = { fmls: list nat; proofs_on: bool }
let bypass (g:goal) (impl: goal -> goal) : goal = if g.proofs_on then g else impl g
let o3 (g:goal) (impl: goal -> goal) : Lemma (requires g.proofs_on) (ensures bypass g impl == g) = ()
let o3b (g:goal) (impl: goal -> goal) : Lemma (requires not g.proofs_on) (ensures bypass g impl == impl g) = ()
