module Z3BvInvertibility

open Z3BvTheory
module U = FStar.UInt

type relation =
  | Eq | Ne | Ult | Ugt | Ule | Uge | Slt | Sgt | Sle | Sge

let holds (#n:pos) (r:relation) (a b:bv n) : bool =
  match r with
  | Eq -> a = b
  | Ne -> a <> b
  | Ult -> a < b
  | Ugt -> a > b
  | Ule -> a <= b
  | Uge -> a >= b
  | Slt -> to_int_signed a < to_int_signed b
  | Sgt -> to_int_signed a > to_int_signed b
  | Sle -> to_int_signed a <= to_int_signed b
  | Sge -> to_int_signed a >= to_int_signed b

let unconstrained_condition (#n:pos) (r:relation) (t:bv n) : bool =
  match r with
  | Ult -> t <> 0
  | Ugt -> t <> U.ones n
  | Slt -> t <> pow2 (n - 1)
  | Sgt -> t <> pow2 (n - 1) - 1
  | _ -> true

let target (#n:pos) (r:relation) (t:bv n) : bv n =
  match r with
  | Ne -> if t = 0 then 1 else 0
  | Ult -> 0
  | Ugt -> U.ones n
  | Slt -> U.pow2_n #n (n - 1)
  | Sgt -> U.pow2_n #n (n - 1) - 1
  | _ -> t

let lemma_target (#n:pos) (r:relation) (t:bv n)
  : Lemma (unconstrained_condition r t ==> holds r (target r t) t) =
  match r with
  | Eq | Ne | Ult | Ugt | Ule | Uge | Slt | Sgt | Sle | Sge -> ()

let lemma_target_necessary (#n:pos) (r:relation) (a t:bv n)
  : Lemma (holds r a t ==> unconstrained_condition r t) =
  match r with
  | Eq | Ne | Ult | Ugt | Ule | Uge | Slt | Sgt | Sle | Sge -> ()

type bijection = | Neg | Not | Add

let apply_bijection (#n:pos) (op:bijection) (s x:bv n) : bv n =
  match op with
  | Neg -> bvneg x
  | Not -> bvnot x
  | Add -> bvadd x s

let inverse (#n:pos) (op:bijection) (s y:bv n) : bv n =
  match op with
  | Neg -> bvneg y
  | Not -> bvnot y
  | Add -> bvsub y s

let lemma_inverse (#n:pos) (op:bijection) (s y:bv n)
  : Lemma (apply_bijection op s (inverse op s y) == y) =
  match op with
  | Neg -> Z3BvRewriter.lemma_bvneg_involutive y
  | Not -> U.lognot_self y
  | Add -> U.lemma_add_sub_cancel y s

let lemma_bijection_invertibility (#n:pos) (op:bijection)
  (r:relation) (s t:bv n)
  : Lemma
    (unconstrained_condition r t <==>
      (exists (x:bv n). holds r (apply_bijection op s x) t)) =
  lemma_target r t;
  lemma_inverse op s (target r t);
  let x = inverse op s (target r t) in
  assert (unconstrained_condition r t ==> holds r (apply_bijection op s x) t);
  introduce forall x. holds r (apply_bijection op s x) t ==>
    unconstrained_condition r t
  with lemma_target_necessary r (apply_bijection op s x) t

type projection = | And | Or

type unsigned_relation = r:relation{
  r = Eq \/ r = Ne \/ r = Ult \/ r = Ugt \/ r = Ule \/ r = Uge}

let apply_projection (#n:pos) (op:projection) (s x:bv n) : bv n =
  match op with
  | And -> bvand x s
  | Or -> bvor x s

let projection_condition (#n:pos) (op:projection) (r:unsigned_relation) (s t:bv n) : bool =
  match op with
  | And ->
    (match r with
    | Eq -> bvand t s = t
    | Ne -> s <> 0 || t <> 0
    | Ult -> t <> 0
    | Ugt -> t < s
    | Ule -> true
    | Uge -> t <= s
    | _ -> false)
  | Or ->
    (match r with
    | Eq -> bvor t s = t
    | Ne -> s <> U.ones n || t <> U.ones n
    | Ult -> s < t
    | Ugt -> t <> U.ones n
    | Ule -> s <= t
    | Uge -> true
    | _ -> false)

let lemma_projection_bounds (#n:pos) (op:projection) (s x:bv n)
  : Lemma
    (let f = apply_projection op s in
     f 0 <= f x /\ f x <= f (U.ones n) /\
     f (f x) == f x /\
     f 0 == (if op = And then 0 else s) /\
     f (U.ones n) == (if op = And then s else U.ones n)) =
  match op with
  | And ->
    U.logand_commutative 0 s;
    U.logand_commutative (U.ones n) s;
    U.logand_lemma_1 s;
    U.logand_lemma_2 s;
    U.logand_le x s;
    U.logand_associative x s s;
    U.logand_self s
  | Or ->
    U.logor_commutative 0 s;
    U.logor_commutative (U.ones n) s;
    U.logor_lemma_1 s;
    U.logor_lemma_2 s;
    U.logor_ge x s;
    U.logor_associative x s s;
    U.logor_self s

let projection_witness (#n:pos) (op:projection) (r:unsigned_relation) (s t:bv n) : bv n =
  match r with
  | Eq -> t
  | Ne -> if apply_projection op s 0 <> t then 0 else U.ones n
  | Ult | Ule -> 0
  | _ -> U.ones n

#push-options "--fuel 4 --ifuel 1 --z3rlimit 10"
let lemma_projection_sufficient (#n:pos) (op:projection) (r:unsigned_relation) (s t:bv n)
  : Lemma
    (projection_condition op r s t ==>
      holds r (apply_projection op s (projection_witness op r s t)) t) =
  lemma_projection_bounds op s t;
  lemma_projection_bounds op s 0;
  match op with
  | And ->
    (match r with
    | Ult -> lemma_target Ult t
    | Eq | Ne | Ugt | Ule | Uge -> ())
  | Or ->
    (match r with
    | Ugt -> lemma_target Ugt t
    | Eq | Ne | Ult | Ule | Uge -> ())

let lemma_projection_necessary (#n:pos) (op:projection)
  (r:unsigned_relation)
  (s t x:bv n)
  : Lemma (holds r (apply_projection op s x) t ==> projection_condition op r s t) =
  lemma_projection_bounds op s x;
  match op with
  | And ->
    (match r with
    | Ne -> if s = 0 then U.logand_lemma_1 x
    | Eq | Ult | Ugt | Ule | Uge -> ())
  | Or ->
    (match r with
    | Ne -> if s = U.ones n then U.logor_lemma_2 x
    | Eq | Ult | Ugt | Ule | Uge -> ())

let lemma_projection_invertibility (#n:pos) (op:projection)
  (r:unsigned_relation)
  (s t:bv n)
  : Lemma
    (projection_condition op r s t <==>
      (exists (x:bv n). holds r (apply_projection op s x) t)) =
  lemma_projection_sufficient op r s t;
  let x = projection_witness op r s t in
  assert (projection_condition op r s t ==> holds r (apply_projection op s x) t);
  introduce forall x. holds r (apply_projection op s x) t ==>
    projection_condition op r s t
  with lemma_projection_necessary op r s t x
#pop-options

let lemma_ashr_large (#n:pos) (a:bv n) (s:nat{s >= n})
  : Lemma (bvashr a s == (if msb a then U.ones n else 0)) =
  U.shift_right_value_lemma a s;
  U.shift_right_value_lemma (bvnot a) s;
  U.lognot_lemma_1 #n

let lemma_sign_extend_value (#n:pos) (k:nat) (a:bv n)
  : Lemma
    (bv_sign_extend k a ==
      (if msb a then a + pow2 (n + k) - pow2 n else a)) =
  if k > 0 then (
    U.lemma_zero_extends k a;
    U.lemma_lognot_value_mod a;
    U.lemma_zero_extends k (bvnot a);
    U.lemma_lognot_value_mod #(n + k) (bv_zero_extend k (bvnot a))
  )

let lemma_sign_extend_signed (#n:pos) (k:nat) (a:bv n)
  : Lemma (to_int_signed (bv_sign_extend k a) == to_int_signed a) =
  lemma_sign_extend_value k a;
  FStar.Math.Lemmas.pow2_le_compat (n + k - 1) (n - 1);
  FStar.Math.Lemmas.pow2_double_mult (n - 1);
  FStar.Math.Lemmas.pow2_double_mult (n + k - 1);
  if msb a then
    assert (msb (bv_sign_extend k a))
  else
    assert (not (msb (bv_sign_extend k a)))
