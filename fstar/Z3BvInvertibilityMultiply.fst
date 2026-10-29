module Z3BvInvertibilityMultiply

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module P = Z3BvInvertibilityProofs
module B = Z3BvInvertibilityBits
module S = Z3BvInvertibilitySigned
module C = Z3BvInvertibilityCarry
module F = Z3BvInvertibilityFactors
module R = Z3BvInvertibilityRemainder
module M = FStar.Math.Lemmas

let mask (#n:pos) (s:bv n) : bv n = bvor (bvneg s) s

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_factor_mask (#n:pos) (s:bv n{s > 0}) (f:F.factorization n s)
  : Lemma (let (| k, _ |) = f in
      mask s == bvnot #n (U.pow2_n #n k - 1) /\
      mask s == pow2 n - pow2 k /\ mask s >= signed_min n) =
  let (| k, _ |) = f in
  F.lemma_mask #n k 0;
  U.logor_commutative s (bvneg s);
  M.pow2_le_compat (n - 1) k;
  M.pow2_double_mult (n - 1);
  assert_norm (signed_min n == pow2 (n - 1))

let lemma_mask_zero (#n:pos) (s:bv n)
  : Lemma (mask s == 0 <==> s == 0) =
  R.lemma_neg_value s;
  U.logor_lemma_1 #n 0;
  if s > 0 then (
    let f = F.factor n s in
    lemma_factor_mask s f;
    M.pow2_double_mult (n - 1)
  )

let lemma_product_projection (#n:pos) (s x:bv n)
  : Lemma (bvand (bvmul x s) (mask s) == bvmul x s) =
  if s > 0 then (
    let f = F.factor n s in
    let (| k, _ |) = f in
    lemma_factor_mask s f;
    F.lemma_product_multiple s f x;
    F.lemma_mask k (bvmul x s)
  )
  else (
    assert (s == 0);
    F.lemma_mul_value x s;
    U.logand_commutative 0 (mask s);
    U.logand_lemma_1 (mask s)
  )

let projection_preimage (#n:pos) (s x:bv n)
  : Tot (y:bv n{bvmul y s == bvand x (mask s)}) =
  if s > 0 then (
    let f = F.factor n s in
    let (| k, _ |) = f in
    lemma_factor_mask s f;
    F.lemma_mask k x;
    M.lemma_div_mod x (pow2 k);
    M.cancel_mul_mod (x / pow2 k) (pow2 k);
    F.multiple_preimage s f (bvand x (mask s))
  )
  else (
    assert (s == 0);
    lemma_mask_zero s;
    U.logand_lemma_1 x;
    F.lemma_mul_value #n 0 s;
    0
  )

let lemma_mask_signed_max (#n:pos) (k:nat{k < n})
  (a:bv n{a == pow2 n - pow2 k})
  : Lemma (bvand a (signed_max n) == pow2 (n - 1) - pow2 k) =
  assert_norm (signed_max n == pow2 (n - 1) - 1);
  F.lemma_mask k (signed_max n);
  U.logand_commutative a (signed_max n);
  M.pow2_plus (n - 1 - k) k;
  M.distributivity_sub_left (pow2 (n - 1 - k)) 1 (pow2 k);
  M.modulo_addition_lemma (pow2 k - 1) (pow2 k) (pow2 (n - 1 - k) - 1);
  M.modulo_lemma (pow2 k - 1) (pow2 k)

let lemma_next_multiple (#n:pos) (k:nat{k < n})
  (a:bv n{a == pow2 n - pow2 k}) (t:bv n)
  : Lemma (I.holds I.Slt t (bvsub t (bvor a t)) <==>
      I.holds I.Slt t (bvand a (signed_max n))) =
  F.lemma_mask k t;
  lemma_mask_signed_max k a;
  U.logand_commutative a t;
  C.lemma_and_or_sum a t;
  C.lemma_sub_value t (bvor a t);
  M.pow2_le_compat (n - 1) k;
  M.pow2_double_mult (n - 1);
  M.pow2_plus (n - 1 - k) k;
  M.distributivity_sub_left (pow2 (n - 1 - k)) 1 (pow2 k);
  let r = t % pow2 k in
  let v = t - r + pow2 k in
  M.modulo_addition_lemma (v - pow2 n) (pow2 n) 1;
  if t < pow2 (n - 1) - pow2 k then
    M.modulo_lemma v (pow2 n)
  else if t < pow2 (n - 1) then (
    M.modulo_addition_lemma (t - pow2 (n - 1) + pow2 k) (pow2 k)
      (pow2 (n - 1 - k) - 1);
    M.modulo_lemma (t - pow2 (n - 1) + pow2 k) (pow2 k);
    M.modulo_lemma v (pow2 n)
  )
  else if v < pow2 n then M.modulo_lemma v (pow2 n)
  else M.modulo_lemma (v - pow2 n) (pow2 n)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_projection_sge_max (#n:pos) (a t:bv n)
  : Lemma (condition Conjoin I.Sge a t <==>
      I.holds I.Sge (bvand a (signed_max n)) t) =
  C.lemma_and_successor a t;
  B.lemma_and_signed_bounds a t;
  B.lemma_and_signed_bounds a (bvsub t a);
  U.logand_commutative a t;
  U.logand_commutative a (signed_max n)

#push-options "--fuel 2 --ifuel 1"
let lemma_source_correspondence (#n:pos) (r:I.relation) (s t:bv n)
  : Lemma (condition Multiply r s t <==> condition Conjoin r (mask s) t) =
  C.lemma_range s;
  if s > 0 then (
    let f = F.factor n s in
    let (| k, _ |) = f in
    lemma_factor_mask s f;
    C.lemma_range t;
    U.lemma_uint_mod #n 0;
    U.logor_commutative s (bvneg s);
    U.logand_commutative t (mask s);
    U.logand_commutative s t;
    lemma_mask_zero s;
    lemma_projection_sge_max (mask s) t;
    B.lemma_sign_mask t;
    M.pow2_double_mult (n - 1);
    U.logor_associative s t (bvneg s);
    U.logor_commutative t (bvneg s);
    U.logor_associative s (bvneg s) t;
    lemma_next_multiple k (mask s) t;
    match r with
    | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge
    | I.Slt | I.Sgt | I.Sle | I.Sge -> ()
  )
  else (
    assert (s == 0);
    U.lemma_uint_mod #n 0;
    lemma_mask_zero s;
    lemma_projection_sge_max (mask s) t;
    B.lemma_sign_mask t;
    M.pow2_double_mult (n - 1);
    R.lemma_neg_value s;
    U.logor_lemma_1 #n 0;
    U.logor_commutative 0 t;
    U.logor_lemma_1 t;
    U.logand_commutative 0 t;
    U.logand_lemma_1 t;
    U.logand_lemma_1 (bvnot (bvneg t));
    U.logand_commutative 0 (signed_max n);
    U.logand_lemma_1 (signed_max n);
    C.lemma_sub_value t t;
    match r with
    | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge
    | I.Slt | I.Sgt | I.Sle | I.Sge -> ()
  )
#pop-options

let lemma_projection_conditions (#n:pos) (r:I.relation) (a t:bv n)
  : Lemma (condition Conjoin r a t <==>
      (exists (x:bv n). I.holds r (bvand x a) t)) =
  match r with
  | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge ->
    P.lemma_projections Conjoin r a t
  | I.Slt -> S.lemma_and_slt a t
  | I.Sgt -> S.lemma_and_sgt a t
  | I.Sle -> S.lemma_and_sle a t
  | I.Sge -> C.lemma_and_sge a t

let lemma_product_image (#n:pos) (r:I.relation) (s t:bv n)
  : Lemma
    ((exists (x:bv n). I.holds r (bvmul x s) t) <==>
     (exists (x:bv n). I.holds r (bvand x (mask s)) t)) =
  (introduce forall x. I.holds r (bvmul x s) t ==>
    (exists (y:bv n). I.holds r (bvand y (mask s)) t)
  with (
    lemma_product_projection s x;
    let y = bvmul x s in
    assert (I.holds r (bvmul x s) t ==> I.holds r (bvand y (mask s)) t)
  ));
  introduce forall x. I.holds r (bvand x (mask s)) t ==>
    (exists (y:bv n). I.holds r (bvmul y s) t)
  with (
    let y = projection_preimage s x in
    assert (I.holds r (bvand x (mask s)) t ==> I.holds r (bvmul y s) t)
  )

let lemma_multiply (#n:pos) (r:I.relation) (s t:bv n)
  : Lemma (condition Multiply r s t <==>
      (exists (x:bv n). I.holds r (apply Multiply s x) t)) =
  lemma_source_correspondence r s t;
  lemma_projection_conditions r (mask s) t;
  lemma_product_image r s t
#pop-options
