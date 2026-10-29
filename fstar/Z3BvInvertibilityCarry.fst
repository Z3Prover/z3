module Z3BvInvertibilityCarry

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module A = Z3BvInvertibilityArithmetic
module B = Z3BvInvertibilityBits
module R = Z3BvInvertibilityRemainder
module M = FStar.Math.Lemmas
module Q = FStar.Seq.Base
module QP = FStar.Seq.Properties

#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let lemma_range (#n:pos) (a:bv n) : Lemma (0 <= a /\ a < pow2 n) = ()

let prefix (#n:pos) (a:bv n) (k:nat{k <= n}) : U.uint_t k =
  U.from_vec #k (Q.slice (U.to_vec a) 0 k)

let lemma_prefix_step (#n:pos) (a:bv n) (k:pos{k <= n})
  : Lemma (prefix a k ==
      2 * prefix a (k - 1) + (if U.nth a (k - 1) then 1 else 0)) =
  QP.slice_slice (U.to_vec a) 0 k 0 (k - 1);
  Q.lemma_index_slice (U.to_vec a) 0 k (k - 1)

let lemma_prefix_zero (#n:pos) (a:bv n) : Lemma (prefix a 0 == 0) = ()

#push-options "--fuel 0 --ifuel 0"
let rec lemma_prefix_sum (#n:pos) (a b:bv n) (k:nat{k <= n})
  : Lemma
    (prefix (bvand a b) k + prefix (bvor a b) k == prefix a k + prefix b k)
    (decreases k) =
  assert_norm (bvand a b == U.logand a b);
  assert_norm (bvor a b == U.logor a b);
  if k > 0 then (
    lemma_prefix_sum a b (k - 1);
    lemma_prefix_step a k;
    lemma_prefix_step b k;
    lemma_prefix_step (bvand a b) k;
    lemma_prefix_step (bvor a b) k;
    U.logand_definition a b (k - 1);
    U.logor_definition a b (k - 1)
  )
  else (
    lemma_prefix_zero a;
    lemma_prefix_zero b;
    lemma_prefix_zero (bvand a b);
    lemma_prefix_zero (bvor a b)
  )
#pop-options

let lemma_and_or_sum (#n:pos) (a b:bv n)
  : Lemma (bvand a b + bvor a b == a + b) =
  lemma_prefix_sum a b n;
  QP.slice_length (U.to_vec a);
  QP.slice_length (U.to_vec b);
  QP.slice_length (U.to_vec (bvand a b));
  QP.slice_length (U.to_vec (bvor a b));
  U.inverse_num_lemma a;
  U.inverse_num_lemma b;
  U.inverse_num_lemma (bvand a b);
  U.inverse_num_lemma (bvor a b)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_sub_value (#n:pos) (a b:bv n)
  : Lemma (bvsub a b == (if a >= b then a - b else pow2 n + a - b)) =
  if a >= b then M.modulo_lemma (a - b) (pow2 n)
  else (
    M.modulo_addition_lemma (a - b) (pow2 n) 1;
    M.modulo_lemma (pow2 n + a - b) (pow2 n)
  )

let lemma_or_minimum (#n:pos) (s:bv n)
  : Lemma (bvor (signed_min n) s ==
      (if msb s then s else s + pow2 (n - 1))) =
  assert_norm (signed_min n == pow2 (n - 1));
  assert_norm (signed_max n == pow2 (n - 1) - 1);
  B.lemma_de_morgan (signed_min n) s;
  U.lemma_lognot_value_mod (signed_min n);
  U.lemma_lognot_value_mod s;
  U.lemma_lognot_value_mod (bvor (signed_min n) s);
  U.logand_commutative (bvnot (signed_min n)) (bvnot s);
  B.lemma_clear_sign (bvnot s);
  M.pow2_double_mult (n - 1);
  if msb s then M.modulo_lemma (bvnot s) (pow2 (n - 1))
  else (
    M.modulo_addition_lemma (pow2 (n - 1) - 1 - s) (pow2 (n - 1)) 1;
    M.modulo_lemma (pow2 (n - 1) - 1 - s) (pow2 (n - 1))
  )

let lemma_or_predecessor (#n:pos) (s t:bv n)
  : Lemma
    (to_int_signed (bvor (signed_min n) s) < to_int_signed t ==>
      to_int_signed (bvor (bvnot (bvsub s t)) s) < to_int_signed t) =
  lemma_sub_value s t;
  U.lemma_lognot_value_mod (bvsub s t);
  lemma_and_or_sum (bvnot (bvsub s t)) s;
  lemma_range (bvand (bvnot (bvsub s t)) s);
  lemma_range (bvor (bvnot (bvsub s t)) s);
  lemma_or_minimum s;
  B.lemma_bitwise_sign (bvnot (bvsub s t)) s;
  M.pow2_double_mult (n - 1)

let lemma_and_successor (#n:pos) (s t:bv n)
  : Lemma
    (to_int_signed t <= to_int_signed (bvand (signed_max n) s) ==>
      bvand s t == t \/
      to_int_signed t < to_int_signed (bvand (bvsub t s) s)) =
  lemma_sub_value t s;
  lemma_and_or_sum (bvsub t s) s;
  lemma_range (bvand (bvsub t s) s);
  lemma_range (bvor (bvsub t s) s);
  U.logand_commutative (signed_max n) s;
  B.lemma_clear_sign s;
  B.lemma_bitwise_sign (bvsub t s) s;
  M.pow2_double_mult (n - 1);
  if msb t then ()
  else if t = bvand s (signed_max n) then (
    U.logand_commutative s t;
    U.logand_associative s (signed_max n) s;
    U.logand_commutative (signed_max n) s;
    U.logand_self s;
    U.logand_associative (signed_max n) s s
  )
  else if msb s then (
    M.modulo_addition_lemma (s - signed_min n) (signed_min n) 1;
    M.modulo_lemma (s - signed_min n) (signed_min n)
  )
  else M.modulo_lemma s (signed_min n)

let lemma_remainder_eq_condition (#n:pos) (s t:bv n)
  : Lemma (bvand (bvsub (bvadd t t) s) s >= t <==>
      t == s \/ 2 * t < s) =
  let a = bvsub (bvadd t t) s in
  lemma_and_or_sum a s;
  lemma_range (bvor a s);
  U.logand_le a s;
  M.lemma_mod_plus_distr_l (2 * t) (-s) (pow2 n);
  assert (a == (2 * t - s) % pow2 n);
  if 2 * t < s then (
    M.modulo_addition_lemma (2 * t - s) (pow2 n) 1;
    M.modulo_lemma (pow2 n + 2 * t - s) (pow2 n)
  )
  else if 2 * t - s < pow2 n then (
    M.modulo_lemma (2 * t - s) (pow2 n);
    if s = t then U.logand_self t
  )
  else (
    M.modulo_addition_lemma (2 * t - s - pow2 n) (pow2 n) 1;
    M.modulo_lemma (2 * t - s - pow2 n) (pow2 n)
  )
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_or_slt (#n:pos) (s t:bv n)
  : Lemma (condition Disjoin I.Slt s t <==>
      (exists (x:bv n). I.holds I.Slt (apply Disjoin s x) t)) =
  lemma_or_predecessor s t;
  let x = bvnot (bvsub s t) in
  assert (condition Disjoin I.Slt s t ==> I.holds I.Slt (apply Disjoin s x) t);
  introduce forall x.
    to_int_signed (bvor (signed_min n) s) <= to_int_signed (bvor x s)
  with B.lemma_or_signed_bounds s x

let lemma_and_sge (#n:pos) (s t:bv n)
  : Lemma (condition Conjoin I.Sge s t <==>
      (exists (x:bv n). I.holds I.Sge (apply Conjoin s x) t)) =
  lemma_and_successor s t;
  let x = if bvand s t = t then t else bvsub t s in
  U.logand_commutative s t;
  assert (condition Conjoin I.Sge s t ==> I.holds I.Sge (apply Conjoin s x) t);
  introduce forall x.
    to_int_signed (bvand x s) <= to_int_signed (bvand (signed_max n) s)
  with B.lemma_and_signed_bounds s x

let remainder_eq_witness (#n:pos) (s t:bv n) : bv n =
  if t = s then 0 else bvsub s t

let lemma_remainder_eq_attained (#n:pos) (s t:bv n{t == s \/ 2 * t < s})
  : Lemma (apply RemainderDivisor s (remainder_eq_witness s t) == t) =
  lemma_sub_value s t;
  if t <> s then (
    M.division_definition s (s - t) 1
  )

let lemma_remainder_divisor_eq (#n:pos) (s t:bv n)
  : Lemma (condition RemainderDivisor I.Eq s t <==>
      (exists (x:bv n). I.holds I.Eq (apply RemainderDivisor s x) t)) =
  lemma_remainder_eq_condition s t;
  assert (condition RemainderDivisor I.Eq s t <==> (t == s \/ 2 * t < s));
  if condition RemainderDivisor I.Eq s t then lemma_remainder_eq_attained s t;
  let x = remainder_eq_witness s t in
  assert (condition RemainderDivisor I.Eq s t ==>
    I.holds I.Eq (apply RemainderDivisor s x) t);
  introduce forall x.
    (let y = apply RemainderDivisor s x in y == s \/ 2 * y < s)
  with A.lemma_proper_remainder s x
#pop-options
