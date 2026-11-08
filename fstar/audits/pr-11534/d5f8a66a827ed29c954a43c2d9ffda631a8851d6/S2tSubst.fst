module S2tSubst
(* Abstract model of solver2tactic l_false path at head d5f8a66a.
   Formulas are nats. A proof is a leaf asserted(f) or a node with recorded fact. *)
open FStar.List.Tot

type proof =
  | Asserted : f:nat -> proof
  | Node : fact:nat -> kids:list proof -> proof
  | GoalPr : fact:nat -> proof   (* an input goal proof, opaque *)

let fact (p:proof) : nat =
  match p with
  | Asserted f -> f
  | Node f _ -> f
  | GoalPr f -> f

(* environment: pairs (clause i, goal proof i) *)
type env = list (nat & proof)

let rec lookup (e:env) (f:nat) : option proof =
  match e with
  | [] -> None
  | (g,p)::t -> if g = f then Some p else lookup t f

(* expr_safe_replace on Asserted leaves; node facts are stored, so unchanged *)
let rec subst (e:env) (p:proof) : Tot proof (decreases p) =
  match p with
  | Asserted f -> (match lookup e f with Some q -> q | None -> p)
  | Node f ks -> Node f (subst_list e ks)
  | GoalPr _ -> p
and subst_list (e:env) (ks:list proof) : Tot (list proof) (decreases ks) =
  match ks with
  | [] -> []
  | k::t -> subst e k :: subst_list e t

(* per-assertion check in C++: goal proof i has fact = form i *)
let rec wf (e:env) : bool =
  match e with
  | [] -> true
  | (f,p)::t -> fact p = f && wf t

let rec lookup_fact (e:env) (f:nat) : Lemma (requires wf e)
  (ensures (match lookup e f with Some q -> fact q = f | None -> true)) =
  match e with [] -> () | (_,_)::t -> lookup_fact t f

(* O3: with duplicates (insert overwrites), whichever proof is found has fact = formula *)
let o3 (e:env) (f:nat) : Lemma (requires wf e)
  (ensures (match lookup e f with Some q -> fact q = f | None -> true)) = lookup_fact e f

(* O2: substitution preserves the root fact (so is_false check before substitution stays valid) *)
let o2 (e:env) (p:proof) : Lemma (requires wf e) (ensures fact (subst e p) = fact p) =
  match p with
  | Asserted f -> lookup_fact e f
  | _ -> ()

(* O1: guard logic. proofs on: success => no assumptions, root fact false (0), every goal proof matches *)
type outcome =
  | Throw
  | Succeed
let l_false_path (proofs:bool) (nassum:nat) (has_pr:bool) (root:nat) (e:env) : outcome =
  if proofs && nassum > 0 then Throw
  else if proofs && (not has_pr || root <> 0) then Throw
  else if proofs && not (wf e) then Throw
  else Succeed

let o1 (nassum:nat) (has_pr:bool) (root:nat) (e:env)
  : Lemma (l_false_path true nassum has_pr root e = Succeed ==> (nassum = 0 /\ has_pr /\ root = 0 /\ wf e)) = ()
