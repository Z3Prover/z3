module Z3PR11547Throw
(* Abstract model of PR 11547 head 42d5aa89: tactics that cannot produce proofs
   now throw instead of returning the input unchanged. *)
type goal = { proofs:bool; id:int }
type outcome = | Throw | Ret : goal -> outcome

(* fail_if_proof_generation *)
let fail_if_proof (g:goal) : outcome = if g.proofs then Throw else Ret g

(* par_and_then_tactical::operator(): use_seq is always false, then fail_if_proof_generation *)
let par_then (par:goal -> goal) (g:goal) : outcome =
  let use_seq = false in
  if use_seq then Ret g (* sequential path, unreachable *)
  else (match fail_if_proof g with Throw -> Throw | Ret g' -> Ret (par g'))

(* O1: in proof mode par_then never returns a goal (no unsound result possible) *)
let o1 (par:goal -> goal) (g:goal)
  : Lemma (requires g.proofs) (ensures par_then par g == Throw) = ()
(* O2: without proofs, behaviour equals the parallel path *)
let o2 (par:goal -> goal) (g:goal)
  : Lemma (requires not g.proofs) (ensures par_then par g == Ret (par g)) = ()
(* O3 (regression witness): the former sequential fallback result is no longer returned in proof mode *)
let o3 (par:goal -> goal) (g:goal)
  : Lemma (requires g.proofs) (ensures par_then par g =!= Ret g) = ()

(* smt_tactic l_false case: proof mode requires a proof whose fact is false *)
noeq type pr = | NoPr | Pr : fact_false:bool -> pr
let smt_false (prf:pr) (g:goal) : outcome =
  if g.proofs && (match prf with NoPr -> true | Pr f -> not f) then Throw else Ret g
(* O4: unchanged goal is never returned as an unsat result without a false proof *)
let o4 (prf:pr) (g:goal)
  : Lemma (requires g.proofs /\ (NoPr? prf \/ (Pr? prf /\ not (Pr?.fact_false prf))))
          (ensures smt_false prf g == Throw) = ()
(* O5: with a false proof, or no proofs, behaviour continues *)
let o5 (prf:pr) (g:goal)
  : Lemma (requires not g.proofs \/ (Pr? prf /\ Pr?.fact_false prf)) (ensures smt_false prf g == Ret g) = ()

(* per-tactic move of guard: previous early-return-unchanged vs now throw *)
let o6 (g:goal) : Lemma (requires g.proofs) (ensures fail_if_proof g == Throw) = ()
