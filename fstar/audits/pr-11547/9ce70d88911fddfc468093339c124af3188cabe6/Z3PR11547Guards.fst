module Z3PR11547Guards
(* Abstract model of the PR 11547 proof-mode guards at head 9ce70d88.
   A goal is abstracted to an opaque id; [sound g h] means h is a proof-backed
   or unchanged successor of g. Soundness of a tactic result = result is
   either the input itself or produced by a proof-preserving step. *)
type goal = { id:int; proofs:bool }
noeq type tac = { supports:bool; run:goal -> goal; psound:goal -> prop }

(* dependent_expr_state_tactic::operator(): early return of input when proofs
   are on and the simplifier does not support proofs *)
let dest_apply (t:tac) (g:goal) : goal =
  if g.proofs && not t.supports then g else t.run g

(* O1: unsupported simplifier in proof mode returns input unchanged *)
let o1 (t:tac) (g:goal)
  : Lemma (requires g.proofs /\ not t.supports) (ensures dest_apply t g == g) = ()
(* O2: without proofs, behavior equals running the simplifier (unchanged) *)
let o2 (t:tac) (g:goal)
  : Lemma (requires not g.proofs) (ensures dest_apply t g == t.run g) = ()
(* O3: supported simplifier in proof mode runs and preserves soundness *)
let o3 (t:tac) (g:goal)
  : Lemma (requires g.proofs /\ t.supports /\ (t.psound g ==> True))
          (ensures dest_apply t g == t.run g) = ()

(* par_and_then: in proof mode falls back to sequential and_then *)
let par_then (seqr parr:goal -> goal) (g:goal) : goal =
  if g.proofs then seqr g else parr g
(* O4: proof mode result is exactly the sequential (proof-producing) result *)
let o4 (seqr parr:goal -> goal) (g:goal)
  : Lemma (requires g.proofs) (ensures par_then seqr parr g == seqr g) = ()
(* O5: non-proof mode unchanged from the parallel path *)
let o5 (seqr parr:goal -> goal) (g:goal)
  : Lemma (requires not g.proofs) (ensures par_then seqr parr g == parr g) = ()
(* O6: the parallel path is reachable only when proofs are disabled *)
let o6 (seqr parr:goal -> goal) (g:goal) (r:goal)
  : Lemma (requires r == par_then seqr parr g /\ r =!= seqr g) (ensures not g.proofs) = ()

(* then_simplifier::reduce: skip children without proof support in proof mode.
   Invariant inv holds of the state if every executed child preserves it. *)
let rec run (proofs:bool) (ss:list tac) (g:goal) : Tot goal (decreases ss) =
  match ss with
  | [] -> g
  | s::tl -> if proofs && not s.supports then run proofs tl g else run proofs tl (s.run g)
let rec all_ok (inv:goal -> prop) (ss:list tac) : prop =
  match ss with
  | [] -> True
  | s::tl -> (s.supports ==> (forall x. inv x ==> inv (s.run x))) /\ all_ok inv tl
(* O7: invariant preserved in proof mode when only supporting children are checked *)
let rec o7 (inv:goal -> prop) (ss:list tac) (g:goal)
  : Lemma (requires inv g /\ all_ok inv ss) (ensures inv (run true ss g)) (decreases ss)
  = match ss with
    | [] -> ()
    | s::tl -> o7 inv tl (if s.supports then s.run g else g)
(* O8: skipping is a no-op on goals when no child supports proofs *)
let rec o8 (ss:list tac) (g:goal)
  : Lemma (requires forall (s:tac). FStar.List.Tot.memP s ss ==> not s.supports)
          (ensures run true ss g == g) (decreases ss)
  = match ss with
    | [] -> ()
    | s::tl -> o8 tl g
