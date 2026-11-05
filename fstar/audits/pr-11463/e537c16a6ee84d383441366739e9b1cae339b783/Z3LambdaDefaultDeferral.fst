module Z3LambdaDefaultDeferral
(* Model of theory_array_full::instantiate_lambda_defaults (PR 11463, head e537c16). *)
open FStar.List.Tot

type parent = { p_rel: bool; p_array: bool; p_beta: bool }
type lam = { id: nat; rel: bool; cls1: bool; parents: list parent }

(* Source loop over parents: returns (local, has_parent), breaking on first bad relevant parent *)
let rec scan (local:bool) (hp:bool) (ps:list parent) : Tot (bool & bool) (decreases ps) =
  match ps with
  | [] -> (local, hp)
  | p :: tl ->
    if not p.p_rel then scan local hp tl
    else if p.p_array || not p.p_beta then (false, true)
    else scan local true tl

let skip (l:lam) : bool =
  if not l.rel then true
  else let (loc, hp) = scan l.cls1 false l.parents in loc && hp

let rec all_nonarray_beta (ps:list parent) : bool =
  match ps with [] -> true | p :: t -> (not p.p_rel || (not p.p_array && p.p_beta)) && all_nonarray_beta t
let rec some_rel (ps:list parent) : bool =
  match ps with [] -> false | p :: t -> p.p_rel || some_rel t

(* O1: relevant lambda is skipped iff singleton class, a relevant parent exists, and all relevant parents are non-array beta consumers *)
let rec scan_spec (loc hp:bool) (ps:list parent)
  : Lemma (ensures (let (l',h') = scan loc hp ps in
           if all_nonarray_beta ps then (l' = loc /\ h' = (hp || some_rel ps))
           else (l' = false /\ h' = true)))
          (decreases ps)
  = match ps with [] -> () | p :: t -> if not p.p_rel then scan_spec loc hp t
      else if p.p_array || not p.p_beta then () else scan_spec loc true t

let o1 (l:lam) : Lemma (skip l = (not l.rel || (l.cls1 && some_rel l.parents && all_nonarray_beta l.parents)))
  = scan_spec l.cls1 false l.parents

(* O2: a lambda with an array-family or non-beta relevant parent is never skipped *)
let o2 (l:lam) (p:parent)
  : Lemma (requires l.rel /\ memP p l.parents /\ p.p_rel /\ (p.p_array \/ not p.p_beta))
          (ensures not (skip l))
  = o1 l;
    let rec aux (ps:list parent) : Lemma (requires memP p ps /\ p.p_rel /\ (p.p_array \/ not p.p_beta)) (ensures not (all_nonarray_beta ps)) =
      match ps with [] -> () | q :: t -> if q = p then () else aux t in
    aux l.parents

(* O3: fingerprint-guarded loop; assign abstracts try_assign_eq. FC_CONTINUE (true) on first progress; false only if every non-skipped lambda was attempted. *)
let instantiate (assign: nat -> bool) (fp: list nat) (n:nat) : list nat & bool =
  if mem n fp then (fp, false) else (n :: fp, assign n)

let rec run (assign: nat -> bool) (fp: list nat) (ls: list lam) : Tot (list nat & bool) (decreases ls) =
  match ls with
  | [] -> (fp, false)
  | l :: t -> if skip l then run assign fp t
              else let (fp', r) = instantiate assign fp l.id in
                   if r then (fp', true) else run assign fp' t

let rec run_mono (assign: nat -> bool) (fp: list nat) (ls: list lam)
  : Lemma (ensures (forall x. mem x fp ==> mem x (fst (run assign fp ls)))) (decreases ls)
  = match ls with [] -> () | l :: t ->
      if skip l then run_mono assign fp t
      else let (fp', r) = instantiate assign fp l.id in if r then () else run_mono assign fp' t

let rec o3 (assign: nat -> bool) (fp: list nat) (ls: list lam)
  : Lemma (requires snd (run assign fp ls) = false)
          (ensures (forall (l:lam). memP l ls /\ not (skip l) ==> mem l.id (fst (run assign fp ls))))
          (decreases ls)
  = match ls with [] -> () | l :: t ->
      if skip l then o3 assign fp t
      else begin
        let (fp', r) = instantiate assign fp l.id in
        if r then () else (run_mono assign fp' t; o3 assign fp' t)
      end

(* assert_delayed_axioms: when the new pre-check fires, FC_CONTINUE is returned before any giveup/done path *)
type fc = | FC_DONE | FC_CONTINUE | FC_GIVEUP
let assert_delayed (progress:bool) (rest:fc) : fc = if progress then FC_CONTINUE else rest
let o4 (rest:fc) : Lemma (assert_delayed true rest = FC_CONTINUE /\ assert_delayed false rest = rest) = ()
