module Z3ElimMonotone

#set-options "--z3rlimit 10 --smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open FStar.Real
open FStar.List.Tot
module C = FStar.Classical
module ID = FStar.IndefiniteDescription

(* Value-level audit of elim_monotone.cpp, not a translation of its AST
   traversal. Rows denote the parser's collected affine polynomials. *)

type sort =
  | RealSort
  | BoolSort

noeq type value =
  | RealValue : real -> value
  | BoolValue : bool -> value

type signature = nat -> sort
type model = nat -> value

let has_sort (v:value) (s:sort) : bool =
  match v, s with
  | RealValue _, RealSort | BoolValue _, BoolSort -> true
  | _ -> false

let wf_model (s:signature) (m:model) : prop =
  forall (x:nat). has_sort (m x) (s x)

let real_at (m:model) (x:nat) : real =
  match m x with RealValue r -> r | BoolValue _ -> 0.0R

let bool_at (m:model) (x:nat) : bool =
  match m x with BoolValue b -> b | RealValue _ -> false

let put_real (m:model) (x:nat) (r:real) : model =
  fun y -> if y = x then RealValue r else m y

let lemma_put_real_wf (s:signature) (m:model) (x:nat) (r:real)
  : Lemma (requires wf_model s m /\ s x == RealSort)
          (ensures wf_model s (put_real m x r) /\
                   (forall (y:nat). y <> x ==> put_real m x r y == m y)) =
  let at (y:nat) : Lemma (has_sort (put_real m x r y) (s y)) =
    if y = x then () else ()
  in C.forall_intro at

noeq type row = {
  terms: list (nat & real);
  constant: real;
  strict: bool;
}

let rec sum (ts:list (nat & real)) (m:model) : Tot real (decreases ts) =
  match ts with
  | [] -> 0.0R
  | (x, c) :: tail -> c *. real_at m x +. sum tail m

let rec coefficient (x:nat) (ts:list (nat & real)) : Tot real (decreases ts) =
  match ts with
  | [] -> 0.0R
  | (y, c) :: tail ->
    (if y = x then c else 0.0R) +. coefficient x tail

let rec residual (x:nat) (ts:list (nat & real)) (m:model)
  : Tot real (decreases ts) =
  match ts with
  | [] -> 0.0R
  | (y, c) :: tail ->
    (if y = x then 0.0R else c *. real_at m y) +. residual x tail m

let row_value (r:row) (m:model) : real = r.constant +. sum r.terms m

let row_holds (r:row) (m:model) : prop =
  if r.strict then row_value r m <. 0.0R else row_value r m <=. 0.0R

let rec lemma_row_split (x:nat) (ts:list (nat & real)) (m:model)
  : Lemma (sum ts m == coefficient x ts *. real_at m x +. residual x ts m)
          (decreases ts) =
  match ts with
  | [] -> ()
  | (y, _) :: tail ->
    lemma_row_split x tail m;
    if y = x then () else ()

let rec lemma_residual_update (x:nat) (ts:list (nat & real)) (m:model) (v:real)
  : Lemma (residual x ts (put_real m x v) == residual x ts m)
          (decreases ts) =
  match ts with
  | [] -> ()
  | (y, _) :: tail ->
    lemma_residual_update x tail m v;
    if y = x then () else ()

let bound (x:nat) (r:row{coefficient x r.terms =!= 0.0R}) (m:model) : real =
  (0.0R -. (r.constant +. residual x r.terms m)) /. coefficient x r.terms

let involved (x:nat) (r:row) : GTot bool =
  not (ID.strong_excluded_middle (coefficient x r.terms == 0.0R))

noeq type formula =
  | Literal : bool -> formula
  | Boolean : nat -> formula
  | Compare : row -> formula
  | Not : formula -> formula
  | And : formula -> formula -> formula
  | Or : formula -> formula -> formula
  | Implies : formula -> formula -> formula
  | Ite : formula -> formula -> formula -> formula

let rec real_terms (s:signature) (ts:list (nat & real))
  : Tot prop (decreases ts) =
  match ts with
  | [] -> True
  | (x, _) :: tail -> s x == RealSort /\ real_terms s tail

let rec well_sorted (s:signature) (f:formula) : Tot prop (decreases f) =
  match f with
  | Literal _ -> True
  | Boolean x -> s x == BoolSort
  | Compare r -> real_terms s r.terms
  | Not p -> well_sorted s p
  | And p q | Or p q | Implies p q -> well_sorted s p /\ well_sorted s q
  | Ite c p q -> well_sorted s c /\ well_sorted s p /\ well_sorted s q

let rec holds (f:formula) (m:model) : Tot prop (decreases f) =
  match f with
  | Literal b -> b == true
  | Boolean x -> bool_at m x == true
  | Compare r -> row_holds r m
  | Not p -> ~(holds p m)
  | And p q -> holds p m /\ holds q m
  | Or p q -> holds p m \/ holds q m
  | Implies p q -> holds p m ==> holds q m
  | Ite c p q -> (holds c m ==> holds p m) /\ (~(holds c m) ==> holds q m)

let rec independent (x:nat) (f:formula) : Tot prop (decreases f) =
  match f with
  | Literal _ -> True
  | Boolean y -> y <> x
  | Compare r -> coefficient x r.terms == 0.0R
  | Not p -> independent x p
  | And p q | Or p q | Implies p q -> independent x p /\ independent x q
  | Ite c p q -> independent x c /\ independent x p /\ independent x q

(* A positive coefficient in a positive occurrence requires decreasing x;
   a negative occurrence reverses that direction. *)
let row_allowed (x:nat) (increase positive:bool) (r:row) : prop =
  let c = coefficient x r.terms in
  c == 0.0R \/
  (if increase = positive then c <. 0.0R else c >. 0.0R)

let rec allowed (x:nat) (increase positive:bool) (f:formula)
  : Tot prop (decreases f) =
  match f with
  | Literal _ -> True
  | Boolean y -> y <> x
  | Compare r -> row_allowed x increase positive r
  | Not p -> allowed x increase (not positive) p
  | And p q | Or p q -> allowed x increase positive p /\ allowed x increase positive q
  | Implies p q ->
    allowed x increase (not positive) p /\ allowed x increase positive q
  | Ite c p q ->
    independent x c /\ allowed x increase positive p /\ allowed x increase positive q

let rec erase (x:nat) (positive:bool) (f:formula)
  : GTot formula (decreases f) =
  match f with
  | Literal _ | Boolean _ -> f
  | Compare r -> if involved x r then Literal positive else f
  | Not p -> Not (erase x (not positive) p)
  | And p q -> And (erase x positive p) (erase x positive q)
  | Or p q -> Or (erase x positive p) (erase x positive q)
  | Implies p q -> Implies (erase x (not positive) p) (erase x positive q)
  | Ite c p q -> Ite c (erase x positive p) (erase x positive q)

let rec bounds (x:nat) (f:formula) (m:model)
  : GTot (list real) (decreases f) =
  match f with
  | Literal _ | Boolean _ -> []
  | Compare r -> if involved x r then [bound x r m] else []
  | Not p -> bounds x p m
  | And p q | Or p q | Implies p q -> bounds x p m @ bounds x q m
  | Ite _ p q -> bounds x p m @ bounds x q m

let rec lemma_erase_well_sorted (s:signature) (x:nat) (positive:bool) (f:formula)
  : Lemma (requires well_sorted s f)
          (ensures well_sorted s (erase x positive f))
          (decreases f) =
  match f with
  | Literal _ | Boolean _ -> ()
  | Compare r -> if involved x r then () else ()
  | Not p -> lemma_erase_well_sorted s x (not positive) p
  | And p q | Or p q ->
    lemma_erase_well_sorted s x positive p;
    lemma_erase_well_sorted s x positive q
  | Implies p q ->
    lemma_erase_well_sorted s x (not positive) p;
    lemma_erase_well_sorted s x positive q
  | Ite _ p q ->
    lemma_erase_well_sorted s x positive p;
    lemma_erase_well_sorted s x positive q

let rec extreme (increase:bool) (bs:list real) : GTot real (decreases bs) =
  match bs with
  | [] -> 0.0R
  | [b] -> b
  | b :: tail ->
    let e = extreme increase tail in
    if ID.strong_excluded_middle (b <=. e)
    then (if increase then e else b)
    else (if increase then b else e)

let rec bounded (increase:bool) (v:real) (bs:list real)
  : Tot prop (decreases bs) =
  match bs with
  | [] -> True
  | b :: tail -> (if increase then b <=. v else v <=. b) /\ bounded increase v tail

let rec lemma_bounded_weaken (increase:bool) (a b:real) (bs:list real)
  : Lemma (requires bounded increase a bs /\ (if increase then a <=. b else b <=. a))
          (ensures bounded increase b bs)
          (decreases bs) =
  match bs with [] -> () | _ :: tail -> lemma_bounded_weaken increase a b tail

let rec lemma_extreme (increase:bool) (bs:list real)
  : Lemma (bounded increase (extreme increase bs) bs)
          (decreases bs) =
  match bs with
  | [] | [_] -> ()
  | _ :: tail ->
    lemma_extreme increase tail;
    lemma_bounded_weaken increase (extreme increase tail) (extreme increase bs) tail

let rec lemma_bounded_append (increase:bool) (v:real) (xs ys:list real)
  : Lemma (bounded increase v (xs @ ys) <==>
           bounded increase v xs /\ bounded increase v ys)
          (decreases xs) =
  match xs with [] -> () | _ :: tail -> lemma_bounded_append increase v tail ys

let rec lemma_independent_update (x:nat) (f:formula) (m:model) (v:real)
  : Lemma (requires independent x f)
          (ensures holds f (put_real m x v) <==> holds f m)
          (decreases f) =
  match f with
  | Literal _ | Boolean _ -> ()
  | Compare r ->
    lemma_row_split x r.terms m;
    lemma_row_split x r.terms (put_real m x v);
    lemma_residual_update x r.terms m v
  | Not p -> lemma_independent_update x p m v
  | And p q | Or p q | Implies p q ->
    lemma_independent_update x p m v;
    lemma_independent_update x q m v
  | Ite c p q ->
    lemma_independent_update x c m v;
    lemma_independent_update x p m v;
    lemma_independent_update x q m v

let rec lemma_weakening (x:nat) (positive:bool) (f:formula) (m:model)
  : Lemma (if positive then holds f m ==> holds (erase x positive f) m
           else holds (erase x positive f) m ==> holds f m)
          (decreases f) =
  match f with
  | Literal _ | Boolean _ -> ()
  | Compare r -> if involved x r then () else ()
  | Not p -> lemma_weakening x (not positive) p m
  | And p q | Or p q ->
    lemma_weakening x positive p m;
    lemma_weakening x positive q m
  | Implies p q ->
    lemma_weakening x (not positive) p m;
    lemma_weakening x positive q m
  | Ite _ p q ->
    lemma_weakening x positive p m;
    lemma_weakening x positive q m

let witness (x:nat) (increase:bool) (f:formula) (m:model) : GTot real =
  extreme increase (bounds x f m) +. (if increase then 1.0R else 0.0R -. 1.0R)

let lemma_row_witness (x:nat) (increase positive:bool) (r:row) (m:model) (cap:real)
  : Lemma (requires involved x r /\ row_allowed x increase positive r /\
                     (if increase then bound x r m <=. cap else cap <=. bound x r m))
          (ensures (row_holds r (put_real m x
                     (cap +. (if increase then 1.0R else 0.0R -. 1.0R)))) <==> positive == true) =
  let c = coefficient x r.terms in
  let rest = r.constant +. residual x r.terms m in
  let b = bound x r m in
  let v = cap +. (if increase then 1.0R else 0.0R -. 1.0R) in
  lemma_row_split x r.terms (put_real m x v);
  lemma_residual_update x r.terms m v;
  assert (c *. b +. rest == 0.0R);
  assert (row_value r (put_real m x v) == c *. (v -. b));
  ()

let rec lemma_lift_context (x:nat) (increase positive:bool) (f:formula)
                          (m:model) (cap:real)
  : Lemma (requires allowed x increase positive f /\ bounded increase cap (bounds x f m))
          (ensures holds f (put_real m x (cap +. (if increase then 1.0R else 0.0R -. 1.0R)))
                   <==> holds (erase x positive f) m)
          (decreases f) =
  let v = cap +. (if increase then 1.0R else 0.0R -. 1.0R) in
  match f with
  | Literal _ | Boolean _ -> ()
  | Compare r ->
    if involved x r then lemma_row_witness x increase positive r m cap
    else (
      lemma_row_split x r.terms m;
      lemma_row_split x r.terms (put_real m x v);
      lemma_residual_update x r.terms m v)
  | Not p -> lemma_lift_context x increase (not positive) p m cap
  | And p q | Or p q ->
    lemma_bounded_append increase cap (bounds x p m) (bounds x q m);
    lemma_lift_context x increase positive p m cap;
    lemma_lift_context x increase positive q m cap
  | Implies p q ->
    lemma_bounded_append increase cap (bounds x p m) (bounds x q m);
    lemma_lift_context x increase (not positive) p m cap;
    lemma_lift_context x increase positive q m cap
  | Ite c p q ->
    lemma_independent_update x c m v;
    lemma_bounded_append increase cap (bounds x p m) (bounds x q m);
    lemma_lift_context x increase positive p m cap;
    lemma_lift_context x increase positive q m cap

type step = nat & bool

let rec simplify (steps:list step) (f:formula) : GTot formula (decreases steps) =
  match steps with
  | [] -> f
  | (x, _) :: tail -> simplify tail (erase x true f)

let rec valid (s:signature) (steps:list step) (f:formula)
  : GTot prop (decreases steps) =
  match steps with
  | [] -> True
  | (x, increase) :: tail ->
    s x == RealSort /\ allowed x increase true f /\ valid s tail (erase x true f)

(* Later eliminations are reconstructed first, matching reverse definition
   normalization in the C++ and reverse execution of model-converter entries. *)
let rec reconstruct (steps:list step) (f:formula) (m:model)
  : GTot model (decreases steps) =
  match steps with
  | [] -> m
  | (x, increase) :: tail ->
    let n = reconstruct tail (erase x true f) m in
    put_real n x (witness x increase f n)

let rec untouched (steps:list step) (y:nat) : Tot bool (decreases steps) =
  match steps with [] -> true | (x, _) :: tail -> y <> x && untouched tail y

let rec lemma_reconstruction_frame (steps:list step) (f:formula) (m:model) (y:nat)
  : Lemma (requires untouched steps y)
          (ensures reconstruct steps f m y == m y)
          (decreases steps) =
  match steps with
  | [] -> ()
  | (x, _) :: tail -> lemma_reconstruction_frame tail (erase x true f) m y

let rec lemma_chain_well_sorted (s:signature) (steps:list step) (f:formula)
  : Lemma (requires well_sorted s f)
          (ensures well_sorted s (simplify steps f))
          (decreases steps) =
  match steps with
  | [] -> ()
  | (x, _) :: tail ->
    lemma_erase_well_sorted s x true f;
    lemma_chain_well_sorted s tail (erase x true f)

let rec lemma_chain_weakening (steps:list step) (f:formula) (m:model)
  : Lemma (holds f m ==> holds (simplify steps f) m)
          (decreases steps) =
  match steps with
  | [] -> ()
  | (x, _) :: tail ->
    lemma_weakening x true f m;
    lemma_chain_weakening tail (erase x true f) m

let rec lemma_chain_reconstruction (s:signature) (steps:list step) (f:formula) (m:model)
  : Lemma (requires valid s steps f /\ wf_model s m)
          (ensures wf_model s (reconstruct steps f m) /\
                   (holds f (reconstruct steps f m) <==> holds (simplify steps f) m))
          (decreases steps) =
  match steps with
  | [] -> ()
  | (x, increase) :: tail ->
    lemma_chain_reconstruction s tail (erase x true f) m;
    let n = reconstruct tail (erase x true f) m in
    let bs = bounds x f n in
    lemma_extreme increase bs;
    lemma_lift_context x increase true f n (extreme increase bs);
    lemma_put_real_wf s n x (witness x increase f n)

let satisfiable (s:signature) (f:formula) : prop =
  exists (m:model). wf_model s m /\ holds f m

let lemma_equisatisfiable (s:signature) (steps:list step) (f:formula)
  : Lemma (requires valid s steps f)
          (ensures satisfiable s f <==> satisfiable s (simplify steps f)) =
  let forward (m:model)
    : Lemma ((wf_model s m /\ holds f m) ==> satisfiable s (simplify steps f)) =
    lemma_chain_weakening steps f m
  in
  let backward (m:model)
    : Lemma ((wf_model s m /\ holds (simplify steps f) m) ==> satisfiable s f) =
    let complete (_: (wf_model s m /\ holds (simplify steps f) m))
      : Lemma (satisfiable s f) =
      lemma_chain_reconstruction s steps f m;
      C.exists_intro (fun n -> wf_model s n /\ holds f n) (reconstruct steps f m)
    in C.impl_intro complete
  in
  C.forall_to_exists forward;
  C.forall_to_exists backward

(* Refutation of a stronger, incorrect specification: the identity model
   converter does not preserve models in the reverse direction. *)
let example : formula =
  Compare { terms = [(0, 0.0R -. 1.0R)]; constant = 0.0R; strict = true }

let all_reals : signature = fun _ -> RealSort
let zero_model : model = fun _ -> RealValue 0.0R

let lemma_identity_model_counterexample ()
  : Lemma (wf_model all_reals zero_model /\
           allowed 0 true true example /\
           holds (erase 0 true example) zero_model /\
           ~(holds example zero_model)) = ()

let lemma_strict_slack_is_necessary ()
  : Lemma (~(row_holds
      { terms = [(0, 0.0R -. 1.0R)]; constant = 0.0R; strict = true }
      (put_real zero_model 0 0.0R))) = ()

let lemma_mixed_direction_is_rejected ()
  : Lemma (~(allowed 0 true true
      (And example (Compare { terms = [(0, 1.0R)]; constant = 0.0R; strict = true }))) /\
           ~(allowed 0 false true
      (And example (Compare { terms = [(0, 1.0R)]; constant = 0.0R; strict = true })))) = ()

let lemma_ite_condition_is_not_eliminable ()
  : Lemma (~(allowed 0 true true (Ite example (Literal true) (Literal false)))) = ()
