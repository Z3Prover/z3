module CaseSplitCore
(* Model of next_case_split_core (smt_case_split_queue.cpp, PR head 549aace).
   Queue = list of vars, head = heap minimum (highest activity); sorted by act. *)
open FStar.List.Tot

noeq type st = { assigned: nat -> bool; relevant: nat -> bool; act: nat -> int }

(* first loop: erase assigned minima *)
let rec drop_assigned (s:st) (q:list nat) : Tot (list nat) (decreases q) =
  match q with
  | [] -> []
  | v::r -> if s.assigned v then drop_assigned s r else q

(* best relevant unassigned by strict '>' scan *)
let rec best (s:st) (cur:option nat) (q:list nat) : Tot (option nat) (decreases q) =
  match q with
  | [] -> cur
  | v::r ->
    let better = (not (s.assigned v)) && s.relevant v &&
      (match cur with None -> true | Some c -> s.act v > s.act c) in
    best s (if better then Some v else cur) r

(* returns None for null_bool_var, else chosen var; remaining queue erases chosen *)
let core (s:st) (q:list nat) : option nat =
  match drop_assigned s q with
  | [] -> None
  | m::_ ->
    if s.relevant m then Some m
    else (match best s None (drop_assigned s q) with Some r -> Some r | None -> Some m)

let rec sorted (s:st) (q:list nat) : Tot bool (decreases q) =
  match q with
  | a::r -> (match r with b::_ -> s.act a >= s.act b && sorted s r | [] -> true)
  | [] -> true

let rec exists_unassigned (s:st) (q:list nat) : Tot bool (decreases q) =
  match q with [] -> false | v::r -> (not (s.assigned v)) || exists_unassigned s r

let rec exists_rel (s:st) (q:list nat) : Tot bool (decreases q) =
  match q with [] -> false | v::r -> ((not (s.assigned v)) && s.relevant v) || exists_rel s r

let rec drop_mem (s:st) (q:list nat) (x:nat) : Lemma (requires mem x (drop_assigned s q))
  (ensures mem x q) (decreases q) =
  match q with [] -> () | v::r -> if s.assigned v then drop_mem s r x else ()

let rec drop_unassigned (s:st) (q:list nat) (x:nat)
  : Lemma (ensures (mem x q && not (s.assigned x)) ==> mem x (drop_assigned s q)) (decreases q) =
  match q with [] -> () | v::r -> if s.assigned v then drop_unassigned s r x else ()

let rec best_mem (s:st) (cur:option nat) (q:list nat) (x:nat)
  : Lemma (requires best s cur q == Some x)
          (ensures mem x q \/ cur == Some x) (decreases q) =
  match q with [] -> () | v::r ->
    let better = (not (s.assigned v)) && s.relevant v &&
      (match cur with None -> true | Some c -> s.act v > s.act c) in
    best_mem s (if better then Some v else cur) r x

(* best returns Some iff cur=Some or a relevant unassigned exists; result is relevant unassigned if cur is *)
let rec best_props (s:st) (cur:option nat) (q:list nat)
  : Lemma (requires (match cur with None -> True | Some c -> not (s.assigned c) && s.relevant c))
          (ensures (match best s cur q with
                    | None -> cur == None /\ not (exists_rel s q)
                    | Some x -> not (s.assigned x) && s.relevant x))
          (decreases q) =
  match q with [] -> () | v::r ->
    let better = (not (s.assigned v)) && s.relevant v &&
      (match cur with None -> true | Some c -> s.act v > s.act c) in
    best_props s (if better then Some v else cur) r

(* Obligation 1: null iff no unassigned var; otherwise result is an unassigned queued var. *)
let ob1 (s:st) (q:list nat)
  : Lemma (ensures (match core s q with
                    | None -> not (exists_unassigned s q)
                    | Some x -> mem x q /\ not (s.assigned x))) =
  let d = drop_assigned s q in
  let rec aux (q:list nat) : Lemma (ensures (drop_assigned s q == [] ==> not (exists_unassigned s q))
                                         /\ (match drop_assigned s q with [] -> True | m::_ -> not (s.assigned m)))
    (decreases q) = match q with [] -> () | v::r -> if s.assigned v then aux r else () in
  aux q;
  match d with
  | [] -> ()
  | m::_ ->
    if s.relevant m then drop_mem s q m
    else begin
      best_props s None d;
      match best s None d with
      | Some r -> best_mem s None d r; drop_mem s q r
      | None -> drop_mem s q m
    end

(* Obligation 2: if a relevant unassigned var exists, the result is relevant. *)
let ob2 (s:st) (q:list nat)
  : Lemma (requires exists_rel s q)
          (ensures (match core s q with Some x -> s.relevant x | None -> False)) =
  let rec aux (q:list nat) : Lemma (requires exists_rel s q)
    (ensures exists_rel s (drop_assigned s q)) (decreases q) =
    match q with [] -> () | v::r -> if s.assigned v then aux r else () in
  aux q;
  match drop_assigned s q with
  | [] -> ()
  | m::_ -> if s.relevant m then () else (best_props s None (drop_assigned s q))

(* Obligation 3: on a heap-ordered queue the chosen relevant var has maximal activity
   among all unassigned relevant queued vars. *)
let rec ge_all (s:st) (m:nat) (q:list nat) : Lemma
  (requires sorted s (m::q)) (ensures forall x. mem x q ==> s.act m >= s.act x) (decreases q) =
  match q with [] -> () | v::r -> (match r with [] -> () | _ -> ge_all s v r; ge_all s m r)

let rec best_max (s:st) (cur:option nat) (q:list nat) (x:nat)
  : Lemma (requires best s cur q == Some x)
          (ensures (forall y. (mem y q && not (s.assigned y) && s.relevant y) ==> s.act x >= s.act y)
                /\ (match cur with Some c -> s.act x >= s.act c | None -> True))
          (decreases q) =
  match q with [] -> () | v::r ->
    let better = (not (s.assigned v)) && s.relevant v &&
      (match cur with None -> true | Some c -> s.act v > s.act c) in
    best_max s (if better then Some v else cur) r x

let ob3 (s:st) (q:list nat) (x:nat)
  : Lemma (requires sorted s q /\ core s q == Some x /\ s.relevant x)
          (ensures forall y. (mem y q && not (s.assigned y) && s.relevant y) ==> s.act x >= s.act y) =
  let rec sub (q:list nat) : Lemma (requires sorted s q) (ensures sorted s (drop_assigned s q)) (decreases q) =
    match q with [] -> () | v::r -> if s.assigned v then (match r with [] -> () | _ -> sub r) else () in
  sub q;
  let d = drop_assigned s q in
  let rec dm (q:list nat) (y:nat) : Lemma (ensures (mem y q && not (s.assigned y)) ==> mem y (drop_assigned s q)) (decreases q) =
    match q with [] -> () | v::r -> if s.assigned v then dm r y else () in
  match d with
  | [] -> ()
  | m::t ->
    if s.relevant m then begin
      ge_all s m t;
      let aux (y:nat) : Lemma ((mem y q && not (s.assigned y) && s.relevant y) ==> s.act x >= s.act y) =
        dm q y in
      FStar.Classical.forall_intro aux
    end else begin
      best_props s None d;
      (match best s None d with
       | Some r -> best_max s None d r;
          let aux (y:nat) : Lemma ((mem y q && not (s.assigned y) && s.relevant y) ==> s.act x >= s.act y) = dm q y in
          FStar.Classical.forall_intro aux
       | None -> ())
    end
