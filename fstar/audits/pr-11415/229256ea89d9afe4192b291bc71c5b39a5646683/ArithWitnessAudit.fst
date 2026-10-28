module ArithWitnessAudit
module L = FStar.List.Tot

(* W1: witness fold value = ite(value <= v, value, v) starting from values[0]. *)
let rec fold_min (acc: int) (vs: list int) : Tot int (decreases vs) =
  match vs with
  | [] -> acc
  | v :: tl -> fold_min (if acc <= v then acc else v) tl

let rec fold_min_le (acc: int) (vs: list int)
  : Lemma (ensures fold_min acc vs <= acc /\ (forall (x:int). L.mem x vs ==> fold_min acc vs <= x))
          (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl -> fold_min_le (if acc <= v then acc else v) tl

let rec fold_min_mem (acc: int) (vs: list int)
  : Lemma (ensures fold_min acc vs == acc \/ L.mem (fold_min acc vs) vs)
          (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl -> fold_min_mem (if acc <= v then acc else v) tl

(* the merged witness is a minimum of the collected candidates: below all, and one of them *)
let w1_min (v0: int) (rest: list int)
  : Lemma (let m = fold_min v0 rest in
           (forall (x:int). L.mem x (v0 :: rest) ==> m <= x) /\ L.mem m (v0 :: rest))
  = fold_min_le v0 rest; fold_min_mem v0 rest

(* W2: add_arith_instance dedup + budget. State: emitted list and unsigned budget. *)
let add_inst (emitted: list (list int)) (budget: nat) (t: list int)
  : tuple3 (list (list int)) nat bool =
  if L.mem t emitted then (emitted, budget, false)
  else if budget = 0 then (emitted, budget, false)
  else (t :: emitted, budget - 1, true)

let w2_budget (emitted: list (list int)) (budget: nat) (t: list int)
  : Lemma (let (e', b', r) = add_inst emitted budget t in
           b' <= budget /\
           (r ==> (b' = budget - 1 /\ budget > 0 /\ ~(L.mem t emitted) /\ L.length e' = L.length emitted + 1)) /\
           (not r ==> e' == emitted /\ b' = budget))
  = ()

(* idempotence: re-adding the same instance never charges budget or emits *)
let w2_idempotent (emitted: list (list int)) (budget: nat) (t: list int)
  : Lemma (let (e1, b1, _) = add_inst emitted budget t in
           let (e2, b2, r2) = add_inst e1 b1 t in
           (b1 > 0 \/ L.mem t emitted ==> (e2 == e1 /\ b2 = b1 /\ not r2)))
  = ()

(* W3: guard added in the PR: projected && boundary == 0 returns false before any
   instance; otherwise boundary scaled by 1/(p+1), p<=8, is only emitted when nonzero. *)
let emits (projected: bool) (boundary_is_zero: bool) : bool =
  not (projected && boundary_is_zero)

let w3_no_zero_projected (projected z: bool)
  : Lemma (ensures (projected && z ==> not (emits projected z)) /\ (not projected ==> emits projected z))
  = ()
