module Z3PR11528ProofConverter
(* Abstract model of Z3 proof converters (PR 11528). Proofs are trees; a
   converter maps a list of source proofs to a proof, as in proof_converter.h. *)
open FStar.List.Tot

type proof =
  | Asserted : nat -> proof
  | Hyp : nat -> proof
  | Parent : proof -> proof                       (* stands for any parent converter step *)
  | Split : cls:nat -> list proof -> proof        (* split_pc: unit_resolution over lemmas *)

type conv = list proof -> proof

(* concat_proof_converter: c2 first, then c1 on the single result *)
let concat (c1 c2:conv) : conv = fun src -> c1 [c2 src]

(* split_pc *)
let split_pc (cls:nat) : conv = fun src -> Split cls src

let parent_pc : conv = fun src -> Parent (match src with | [p] -> p | _ -> Asserted 0)

(* subgoal_proof_converter: ignores sources, evaluates each child goal converter *)
let subgoal_pc (pc:conv) (kids:list conv) : conv =
  fun _ -> pc (map (fun (k:conv) -> k []) kids)

(* O1: split registration via add (PR) yields parent(split(children)) *)
let o1 (cls:nat) (kids:list conv) :
  Lemma (subgoal_pc (concat parent_pc (split_pc cls)) kids []
         == Parent (Split cls (map (fun (k:conv) -> k []) kids))) = ()

(* Old behaviour (in->set): parent converter lost. Differs from O1 result. *)
let old_split (cls:nat) (kids:list conv) = subgoal_pc (split_pc cls) kids []
let o1_old_drops_parent (cls:nat) (kids:list conv) :
  Lemma (old_split cls kids =!= Parent (Split cls (map (fun (k:conv) -> k []) kids))) = ()

(* O2: goal::pc() for inconsistent goal with proof pr0 is m_pc applied to pr0;
   with a leaf child whose pr0 is the hypothesis, children evaluate to it. *)
noeq type goal = { pc: option conv; pr0: option proof; incons: bool }

let none_const : conv = fun _ -> Asserted 0
let goal_pc (g:goal) : option conv =
  if not g.incons then g.pc
  else match g.pr0 with
    | None -> None
    | Some p ->
      let leaf : conv = fun _ -> p in
      (match g.pc with None -> Some leaf | Some c -> Some (concat c leaf))

let apply0 (c:option conv) : option proof = match c with None -> None | Some f -> Some (f [])

let o2 (c:conv) (p:proof) :
  Lemma (apply0 (goal_pc {pc=Some c; pr0=Some p; incons=true}) == Some (c [p])) = ()

(* O3: materialization clears the converter, so a second boundary applies nothing *)
let materialize (g:goal) : option proof & goal =
  (apply0 (goal_pc g), {g with pc = None})
let o3 (g:goal) :
  Lemma (requires not g.incons)
        (ensures apply0 (goal_pc (snd (materialize g))) == None) = ()
