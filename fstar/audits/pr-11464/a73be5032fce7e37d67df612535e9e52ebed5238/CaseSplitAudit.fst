module CaseSplitAudit
open FStar.List.Tot

(* Abstract context: assigned/relevant predicates and activity. Queue is a list, head = min_value. *)
noeq type ctx = { assigned: nat -> bool; relevant: nat -> bool; act: nat -> int }

(* while (!empty && assigned(min)) erase_min *)
let rec drop_assigned (c:ctx) (q:list nat) : Tot (list nat) (decreases q) =
  match q with
  | [] -> []
  | x::tl -> if c.assigned x then drop_assigned c tl else q

(* loop over queue choosing strictly-greater activity relevant unassigned var *)
let rec best (c:ctx) (q:list nat) (r:option nat) : Tot (option nat) (decreases q) =
  match q with
  | [] -> r
  | v::tl ->
    let better = (not (c.assigned v)) && c.relevant v &&
      (match r with None -> true | Some w -> c.act v > c.act w) in
    best c tl (if better then Some v else r)

(* next_case_split_core: returns chosen var option *)
let core (c:ctx) (q:list nat) : option nat =
  match drop_assigned c q with
  | [] -> None
  | m::_ -> let q' = drop_assigned c q in
    if c.relevant m then Some m
    else (match best c q' None with Some r -> Some r | None -> Some m)

let rec exists_un (c:ctx) (q:list nat) : bool =
  match q with [] -> false | x::tl -> (not (c.assigned x)) || exists_un c tl
let rec exists_rel (c:ctx) (q:list nat) : bool =
  match q with [] -> false | x::tl -> ((not (c.assigned x)) && c.relevant x) || exists_rel c tl

let rec drop_sub (c:ctx) (q:list nat) : Lemma (ensures (forall x. mem x (drop_assigned c q) ==> mem x q)) (decreases q) =
  match q with [] -> () | x::tl -> if c.assigned x then drop_sub c tl else ()

let rec drop_mem (c:ctx) (q:list nat) : Lemma (ensures ((match drop_assigned c q with
   | [] -> not (exists_un c q)
   | m::_ -> not (c.assigned m) /\ mem m q /\ exists_un c q) /\ (exists_rel c q <==> exists_rel c (drop_assigned c q)))) (decreases q) =
  match q with [] -> () | x::tl -> if c.assigned x then drop_mem c tl else ()

let rec best_inv (c:ctx) (q:list nat) (r:option nat) : Lemma
  (requires (match r with None -> True | Some w -> not (c.assigned w) /\ c.relevant w))
  (ensures (match best c q r with
     | None -> r == None /\ not (exists_rel c q)
     | Some w -> not (c.assigned w) /\ c.relevant w /\ (mem w q \/ r == Some w)))
  (decreases q) =
  match q with [] -> () | v::tl ->
    let better = (not (c.assigned v)) && c.relevant v &&
      (match r with None -> true | Some w -> c.act v > c.act w) in
    best_inv c tl (if better then Some v else r)

(* Obligation 1: None iff every queued var is assigned *)
let ob1 (c:ctx) (q:list nat) : Lemma (None? (core c q) <==> not (exists_un c q)) =
  drop_mem c q

(* Obligation 2: result is unassigned and drawn from the queue *)
let ob2 (c:ctx) (q:list nat) : Lemma
  (match core c q with None -> True | Some v -> not (c.assigned v) /\ mem v q) =
  drop_mem c q; drop_sub c q;
  match drop_assigned c q with
  | [] -> ()
  | m::_ -> let q' = drop_assigned c q in if c.relevant m then () else best_inv c q' None

(* Obligation 3 (new guarantee): if an unassigned relevant var exists, result is relevant *)
let rec best_complete (c:ctx) (q:list nat) (r:option nat) : Lemma
  (requires exists_rel c q \/ Some? r)
  (ensures Some? (best c q r)) (decreases q) =
  match q with [] -> () | v::tl ->
    let better = (not (c.assigned v)) && c.relevant v &&
      (match r with None -> true | Some w -> c.act v > c.act w) in
    let r' = if better then Some v else r in
    if (not (c.assigned v)) && c.relevant v then best_complete c tl r'
    else best_complete c tl r'

let ob3 (c:ctx) (q:list nat) : Lemma
  (requires exists_rel c q)
  (ensures (match core c q with Some v -> c.relevant v | None -> False)) =
  drop_mem c q;
  match drop_assigned c q with
  | [] -> ()
  | m::_ -> let q' = drop_assigned c q in
    if c.relevant m then ()
    else begin best_complete c q' None; best_inv c q' None end
