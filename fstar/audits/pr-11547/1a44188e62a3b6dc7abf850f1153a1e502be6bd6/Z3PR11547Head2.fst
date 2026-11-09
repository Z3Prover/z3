module Z3PR11547Head2
(* Abstract model of PR 11547 at head 1a44188e. A goal is abstracted by its proof-mode flag and an id. *)
type goal = { proofs:bool; id:int }
type outcome = | Throw | Ret : goal -> outcome

(* smt_tactic_core.cpp l_false case: throw unless (not proofs) or proof exists with fact false *)
noeq type pr = | NoPr | Pr : fact_false:bool -> pr
let smt_false (p:pr) (g:goal) : outcome =
  if g.proofs && (match p with NoPr -> true | Pr f -> not f) then Throw else Ret g

(* O1: in proof mode, returning implies a proof of false *)
let o1 (p:pr) (g:goal)
  : Lemma (requires g.proofs /\ Ret? (smt_false p g)) (ensures Pr? p /\ Pr?.fact_false p) = ()
(* O2: without proofs the l_false branch is unchanged *)
let o2 (p:pr) (g:goal)
  : Lemma (requires not g.proofs) (ensures smt_false p g == Ret g) = ()

(* dependent_expr_state_tactic.h: unsupported simplifier + proofs => input returned unchanged *)
noeq type simp = { supports:bool; run:goal -> goal }
let dest (s:simp) (g:goal) : goal = if g.proofs && not s.supports then g else s.run g
(* O3: in proof mode only a proof-supporting simplifier modifies the goal *)
let o3 (s:simp) (g:goal)
  : Lemma (requires g.proofs /\ dest s g =!= g) (ensures s.supports) = ()
(* O4: without proofs behaviour is unchanged *)
let o4 (s:simp) (g:goal) : Lemma (requires not g.proofs) (ensures dest s g == s.run g) = ()

(* then_simplifier::reduce: children lacking proof support are skipped in proof mode *)
let rec run (proofs:bool) (ss:list simp) (g:goal) : Tot goal (decreases ss) =
  match ss with
  | [] -> g
  | s::tl -> if proofs && not s.supports then run proofs tl g else run proofs tl (s.run g)
let rec all_ok (inv:goal -> prop) (ss:list simp) : prop =
  match ss with
  | [] -> True
  | s::tl -> (s.supports ==> (forall (x:goal). inv x ==> inv (s.run x))) /\ all_ok inv tl
(* O5: invariant preserved when only supporting children execute *)
let rec o5 (inv:goal -> prop) (ss:list simp) (g:goal)
  : Lemma (requires inv g /\ all_ok inv ss) (ensures inv (run true ss g)) (decreases ss)
  = match ss with
    | [] -> ()
    | s::tl -> o5 inv tl (if s.supports then s.run g else g)
