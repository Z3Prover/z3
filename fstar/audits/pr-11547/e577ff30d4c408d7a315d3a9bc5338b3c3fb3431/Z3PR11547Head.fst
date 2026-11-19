module Z3PR11547Head
(* Abstract model of PR 11547 at head e577ff30. A goal is abstracted by proof mode flag
   and an id; Ret g is a returned subgoal, Throw is tactic_exception. *)
type goal = { proofs:bool; id:int }
type outcome = | Throw | Ret : goal -> outcome

(* smt_tactic_core.cpp L253: l_false branch *)
noeq type pr = | NoPr | Pr : fact_false:bool -> pr
let smt_false (p:pr) (g:goal) : outcome =
  if g.proofs && (match p with NoPr -> true | Pr f -> not f) then Throw else Ret ({id = g.id; proofs = g.proofs})

(* O1: in proof mode, success of the l_false branch implies a proof whose fact is false *)
let o1 (p:pr) (g:goal)
  : Lemma (requires g.proofs /\ Ret? (smt_false p g)) (ensures Pr? p /\ Pr?.fact_false p) = ()
(* O2: without proofs behaviour is unchanged *)
let o2 (p:pr) (g:goal)
  : Lemma (requires not g.proofs) (ensures smt_false p g == Ret g) = ()
(* O3: no proof or non-false fact in proof mode => Throw *)
let o3 (p:pr) (g:goal)
  : Lemma (requires g.proofs /\ (NoPr? p \/ (Pr? p /\ not (Pr?.fact_false p)))) (ensures smt_false p g == Throw) = ()

(* tactical.cpp L628: par_and_then, use_seq=false, fail_if_proof_generation *)
let fail_if_proof (g:goal) : outcome = if g.proofs then Throw else Ret g
let par_then (par:goal -> goal) (g:goal) : outcome =
  match fail_if_proof g with Throw -> Throw | Ret g' -> Ret (par g')
(* O4: parallel result is never returned in proof mode *)
let o4 (par:goal -> goal) (g:goal) : Lemma (requires g.proofs) (ensures par_then par g == Throw) = ()
let o5 (par:goal -> goal) (g:goal) : Lemma (requires not g.proofs) (ensures par_then par g == Ret (par g)) = ()

(* dependent_expr_state_tactic.h L133: unsupported simplifier + proofs => return input unchanged *)
noeq type simp = { supports:bool; run:goal -> goal }
let dest (s:simp) (g:goal) : goal =
  if g.proofs && not s.supports then g else s.run g
(* O6: in proof mode only a proof-supporting simplifier ever modifies the goal *)
let o6 (s:simp) (g:goal)
  : Lemma (requires g.proofs /\ dest s g =!= g) (ensures s.supports) = ()
let o7 (s:simp) (g:goal) : Lemma (requires not g.proofs) (ensures dest s g == s.run g) = ()

(* then_simplifier::reduce skip: children lacking proof support are skipped in proof mode *)
let rec run (proofs:bool) (ss:list simp) (g:goal) : Tot goal (decreases ss) =
  match ss with
  | [] -> g
  | s::tl -> if proofs && not s.supports then run proofs tl g else run proofs tl (s.run g)
let rec all_ok (inv:goal -> prop) (ss:list simp) : prop =
  match ss with
  | [] -> True
  | s::tl -> (s.supports ==> (forall (x:goal). inv x ==> inv (s.run x))) /\ all_ok inv tl
(* O8: invariant preserved if every executed (supporting) child preserves it *)
let rec o8 (inv:goal -> prop) (ss:list simp) (g:goal)
  : Lemma (requires inv g /\ all_ok inv ss) (ensures inv (run true ss g)) (decreases ss)
  = match ss with
    | [] -> ()
    | s::tl -> o8 inv tl (if s.supports then s.run g else g)
