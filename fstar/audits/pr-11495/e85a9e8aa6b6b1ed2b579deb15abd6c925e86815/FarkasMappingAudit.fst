module FarkasMappingAudit
module L = FStar.List.Tot
open FStar.List.Tot

(* Abstract model of arithmetic_assumptions / AR.assumptions_hold in PR #11495
   (Z3SortedProof.fst:956-979, Z3SortedArithmetic.fst:293-299). t is the truth
   function of a fixed model; a literal is (positive, e). *)
let satisfied (#e:eqtype) (t:e -> bool) (l:bool & e) : bool =
  if fst l then t (snd l) else not (t (snd l))

let rec assumptions_hold (#e:eqtype) (t:e -> bool) (xs:list (bool & e)) : bool =
  match xs with [] -> true | l :: r -> satisfied t l && assumptions_hold t r

let rec truths (#e:eqtype) (t:e -> bool) (xs:list e) : bool =
  match xs with [] -> true | x :: r -> t x && truths t r

let rec any_true (#e:eqtype) (t:e -> bool) (xs:list e) : bool =
  match xs with [] -> false | x :: r -> t x || any_true t r

let pos (#e:eqtype) (x:e) : bool & e = (true, x)
let neg (#e:eqtype) (x:e) : bool & e = (false, x)

let rec lemma_hold_append (#e:eqtype) (t:e -> bool) (xs ys:list (bool & e))
  : Lemma (assumptions_hold t (xs @ ys) == (assumptions_hold t xs && assumptions_hold t ys)) =
  match xs with [] -> () | _ :: r -> lemma_hold_append t r ys

let rec lemma_pos (#e:eqtype) (t:e -> bool) (ps:list e)
  : Lemma (assumptions_hold t (L.map pos ps) == truths t ps) =
  match ps with [] -> () | _ :: r -> lemma_pos t r

let rec lemma_neg (#e:eqtype) (t:e -> bool) (ls:list e)
  : Lemma (assumptions_hold t (L.map neg ls) == not (any_true t ls)) =
  match ls with [] -> () | _ :: r -> lemma_neg t r

(* O1: premises true and no conclusion literal true <=> mapped assumptions hold. *)
let lemma_assumptions (#e:eqtype) (t:e -> bool) (ps ls:list e)
  : Lemma (assumptions_hold t (L.map pos ps @ L.map neg ls) == (truths t ps && not (any_true t ls))) =
  lemma_hold_append t (L.map pos ps) (L.map neg ls); lemma_pos t ps; lemma_neg t ls

(* O2: a checker sound on models satisfying the assumptions yields a sound node. *)
let lemma_node_sound (#e:eqtype) (check: list (bool & e) -> bool)
    (sound: (t:(e -> bool)) -> (xs:list (bool & e)) ->
            Lemma (requires check xs /\ assumptions_hold t xs) (ensures False))
    (t:e -> bool) (ps ls:list e)
  : Lemma (requires check (L.map pos ps @ L.map neg ls) /\ truths t ps)
          (ensures any_true t ls) =
  lemma_assumptions t ps ls;
  if not (any_true t ls) then sound t (L.map pos ps @ L.map neg ls)

(* O3: truths distributes over append. *)
let rec lemma_truths_append (#e:eqtype) (t:e -> bool) (xs ys:list e)
  : Lemma (truths t (xs @ ys) == (truths t xs && truths t ys)) =
  match xs with [] -> () | _ :: r -> lemma_truths_append t r ys
