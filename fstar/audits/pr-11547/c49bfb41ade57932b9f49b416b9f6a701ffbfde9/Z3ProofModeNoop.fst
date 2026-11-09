module Z3ProofModeNoop
(* Abstract model of PR 11547 guards. A goal is a set of assertions viewed through
   its semantic entailment relation; a goal is represented by its "satisfiable" flag
   plus a proof-validity flag. Proof-mode soundness: output goal is either the
   unchanged input, or {false} backed by a proof whose fact is false. *)
type verdict = | LTrue | LFalse | LUndef
noeq type proof = | NoProof | Proof : fact_is_false:bool -> valid:bool -> proof
type goal = { sat: bool; closed_false: bool; has_proof: bool }

(* smt_tactic l_false case (smt_tactic_core.cpp ~L252-275) *)
let smt_false_case (proofs_enabled:bool) (pr:proof) (g:goal) : goal =
  if proofs_enabled && (match pr with NoProof -> true | Proof f _ -> not f) then g
  else { sat = false; closed_false = true; has_proof = proofs_enabled }

(* O1: in proof mode, the goal is closed to false only if a valid proof concluding false exists *)
let o1 (pr:proof) (g:goal)
  : Lemma (requires Proof? pr ==> Proof?.valid pr)
          (ensures (let g' = smt_false_case true pr g in
                    g'.closed_false /\ g'.sat == false ==>
                      (Proof? pr /\ Proof?.fact_is_false pr /\ Proof?.valid pr) \/ (g.closed_false /\ g.sat==false)))
  = ()

(* O2: absent/non-false certificate leaves the goal unchanged (no fabricated 'asserted false') *)
let o2 (pr:proof) (g:goal)
  : Lemma (requires NoProof? pr \/ (Proof? pr /\ not (Proof?.fact_is_false pr)))
          (ensures smt_false_case true pr g == g)
  = ()

(* O3: without proofs, behavior unchanged *)
let o3 (pr:proof) (g:goal)
  : Lemma (ensures (smt_false_case false pr g).closed_false /\ not (smt_false_case false pr g).has_proof)
  = ()

(* then_simplifier::reduce loop: skipping non-proof-capable children preserves
   the invariant "state is valid" if each executed child preserves it. *)
noeq type simp = { supports: bool; step: goal -> goal }
let rec run (proofs:bool) (ss:list simp) (g:goal) : Tot goal (decreases ss) =
  match ss with
  | [] -> g
  | s::tl -> if proofs && not s.supports then run proofs tl g else run proofs tl (s.step g)

let rec all_ok (inv:goal -> prop) (ss:list simp) : prop =
  match ss with
  | [] -> True
  | s::tl -> (s.supports ==> (forall (x:goal). inv x ==> inv (s.step x))) /\ all_ok inv tl

let rec o4 (inv:goal -> prop) (ss:list simp) (g:goal)
  : Lemma (requires inv g /\ all_ok inv ss)
          (ensures inv (run true ss g)) (decreases ss)
  = match ss with
    | [] -> ()
    | s::tl -> o4 inv tl (if s.supports then s.step g else g)
