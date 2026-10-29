module Z3BvInvertibilityFactors

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module B = Z3BvInvertibilityBits
module C = Z3BvInvertibilityCarry
module Remainder = Z3BvInvertibilityRemainder
module M = FStar.Math.Lemmas
module Q = FStar.Seq.Base

#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let lemma_mul_value (#n:pos) (a b:bv n)
  : Lemma (bvmul a b == (a * b) % pow2 n) = ()

let half (#n:pos) (a:bv n) : U.uint_t (n - 1) =
  M.pow2_double_mult (n - 1);
  M.division_propriety a 2;
  a / 2

let lemma_nth_half (#n:pos{n > 1}) (a:bv n) (i:nat{i < n - 1})
  : Lemma (U.nth a i == U.nth #(n - 1) (half a) i) =
  Q.lemma_index_app1 (U.to_vec #(n - 1) (half a))
    (Q.create 1 (a % 2 = 1)) i

let lemma_nth_last (#n:pos) (a:bv n)
  : Lemma (U.nth a (n - 1) == (a % 2 = 1)) =
  Q.lemma_index_app2 (U.to_vec #(n - 1) (half a))
    (Q.create 1 (a % 2 = 1)) (n - 1);
  Q.lemma_index_create 1 (a % 2 = 1) 0

let lemma_or_half (#n:pos{n > 1}) (a b:bv n)
  : Lemma
    (half (bvor a b) == bvor #(n - 1) (half a) (half b) /\
     (bvor a b) % 2 == (if a % 2 = 1 || b % 2 = 1 then 1 else 0)) =
  (introduce forall (i:nat{i < n - 1}).
    U.nth #(n - 1) (half (bvor a b)) i ==
      U.nth #(n - 1) (bvor #(n - 1) (half a) (half b)) i
  with (
    lemma_nth_half a i;
    lemma_nth_half b i;
    lemma_nth_half (bvor a b) i;
    U.logor_definition a b i;
    U.logor_definition #(n - 1) (half a) (half b) i
  ));
  U.nth_lemma #(n - 1) (half (bvor a b)) (bvor #(n - 1) (half a) (half b));
  lemma_nth_last a;
  lemma_nth_last b;
  lemma_nth_last (bvor a b);
  U.logor_definition a b (n - 1);
  M.modulo_range_lemma (bvor a b) 2

let lemma_or_complement (#n:pos) (a:bv n)
  : Lemma (bvor a (bvnot a) == U.ones n) =
  (introduce forall (i:nat{i < n}).
    U.nth (bvor a (bvnot a)) i == U.nth (U.ones n) i
  with (
    U.logor_definition a (bvnot a) i;
    U.lognot_definition a i;
    U.ones_nth_lemma #n i
  ));
  U.nth_lemma (bvor a (bvnot a)) (U.ones n)

let lemma_split_mask (#n:pos) (a m:bv n)
  : Lemma (bvand a m + bvand a (bvnot m) == a) =
  let lo = bvand a m in
  let hi = bvand a (bvnot m) in
  (introduce forall (i:nat{i < n}).
    U.nth (bvor lo hi) i == U.nth a i /\
    U.nth (bvand lo hi) i == U.nth #n 0 i
  with (
    U.logor_definition lo hi i;
    U.logand_definition lo hi i;
    U.logand_definition a m i;
    U.logand_definition a (bvnot m) i;
    U.lognot_definition m i;
    U.zero_nth_lemma #n i
  ));
  U.nth_lemma (bvor lo hi) a;
  U.nth_lemma (bvand lo hi) 0;
  C.lemma_and_or_sum lo hi
#pop-options

type factorization (n:pos) (s:bv n) =
  k:nat{k < n} &
  u:pos{u < pow2 (n - k) /\ u % 2 == 1 /\ s == pow2 k * u /\
    bvor s (bvneg s) == pow2 n - pow2 k}

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let lemma_equal_halves (h:pos) (a b:nat{a < 2 * h /\ b < 2 * h})
  : Lemma (a % h == b % h ==> a == b \/ a + h == b \/ b + h == a) =
  M.lemma_div_mod a h;
  M.lemma_div_mod b h;
  if a < h then M.small_div a h else M.division_definition a h 1;
  if b < h then M.small_div b h else M.division_definition b h 1

let rec factor (n:pos) (s:bv n{s > 0})
  : Tot (factorization n s) (decreases n) =
  C.lemma_range s;
  Remainder.lemma_neg_value s;
  M.pow2_double_mult (n - 1);
  M.lemma_div_mod s 2;
  M.lemma_div_mod (bvneg s) 2;
  M.modulo_range_lemma s 2;
  M.modulo_range_lemma (bvneg s) 2;
  if n = 1 then (
    assert (s == 1);
    U.logor_self s;
    (| 0, s |)
  )
  else (
    lemma_or_half s (bvneg s);
    if s % 2 = 1 then (
      U.lemma_lognot_value_mod #(n - 1) (half s);
      assert (half (bvneg s) == bvnot #(n - 1) (half s));
      lemma_or_complement #(n - 1) (half s);
      M.lemma_div_mod (bvor s (bvneg s)) 2;
      (| 0, s |)
    )
    else (
      let (| k, u |) = factor (n - 1) (half s) in
      Remainder.lemma_neg_value #(n - 1) (half s);
      assert (half (bvneg s) == bvneg #(n - 1) (half s));
      M.lemma_div_mod (bvor s (bvneg s)) 2;
      M.pow2_double_mult k;
      M.paren_mul_right 2 (pow2 k) u;
      (| k + 1, u |)
    )
  )

let rec odd_preimage (n:pos) (s:bv n{s % 2 == 1}) (t:bv n)
  : Tot (x:bv n{bvmul x s == t}) (decreases n) =
  C.lemma_range s;
  C.lemma_range t;
  if n = 1 then (
    assert (s == 1);
    U.lemma_uint_mod t;
    t
  )
  else (
    M.pow2_double_mult (n - 1);
    M.pow2_plus (n - 2) 1;
    M.modulo_modulo_lemma s 2 (pow2 (n - 2));
    let h = pow2 (n - 1) in
    let x = odd_preimage (n - 1) (s % h) (t % h) in
    lemma_mul_value #(n - 1) x (s % h);
    lemma_mul_value #n x s;
    let y = (x * s) % pow2 n in
    M.modulo_range_lemma (x * s) (pow2 n);
    M.lemma_mod_mul_distr_r x s h;
    M.modulo_modulo_lemma (x * s) h 2;
    M.lemma_div_mod y h;
    M.lemma_div_mod t h;
    M.division_propriety y h;
    M.division_propriety t h;
    if y = t then x
    else (
      M.modulo_scale_lemma s h 2;
      M.distributivity_add_left x h s;
      M.modulo_distributivity (x * s) (h * s) (pow2 n);
      M.swap_mul s h;
      lemma_mul_value #n (x + h) s;
      assert (y % h == t % h);
      lemma_equal_halves h y t;
      assert (y == t + h \/ y + h == t);
      if y < t then M.modulo_lemma (y + h) (pow2 n)
      else (
        M.modulo_addition_lemma t (pow2 n) 1;
        M.modulo_lemma t (pow2 n)
      );
      x + h
    )
  )

let lemma_mask (#n:pos) (k:nat{k < n}) (a:bv n)
  : Lemma
    (bvand a (bvnot (U.pow2_n #n k - 1)) == a - a % pow2 k /\
     bvnot #n (U.pow2_n #n k - 1) == pow2 n - pow2 k) =
  let lo:bv n = U.pow2_n #n k - 1 in
  assert_norm (lo == pow2 k - 1);
  U.lemma_lognot_value_mod lo;
  lemma_split_mask a lo;
  if k > 0 then U.logand_mask a k
  else (
    U.logand_lemma_1 a;
    M.cancel_mul_mod a 1
  )

let lemma_scaled_product (#n:pos) (s:bv n{s > 0})
  (f:factorization n s) (x:bv n)
  : Lemma
    (let (| k, u |) = f in
     bvmul x s == ((x * u) % pow2 (n - k)) * pow2 k) =
  let (| k, u |) = f in
  lemma_mul_value x s;
  M.pow2_plus k (n - k);
  M.paren_mul_right x (pow2 k) u;
  M.swap_mul (pow2 k) u;
  M.paren_mul_right x u (pow2 k);
  M.modulo_scale_lemma (x * u) (pow2 k) (pow2 (n - k))

let lemma_product_multiple (#n:pos) (s:bv n{s > 0})
  (f:factorization n s) (x:bv n)
  : Lemma (let (| k, _ |) = f in (bvmul x s) % pow2 k == 0) =
  let (| k, u |) = f in
  lemma_scaled_product s f x;
  M.cancel_mul_mod ((x * u) % pow2 (n - k)) (pow2 k)

let multiple_preimage (#n:pos) (s:bv n{s > 0}) (f:factorization n s)
  (t:bv n{let (| k, _ |) = f in t % pow2 k == 0})
  : Tot (x:bv n{bvmul x s == t}) =
  let (| k, u |) = f in
  M.pow2_plus (n - k) k;
  M.division_propriety t (pow2 k);
  M.distributivity_sub_left (pow2 (n - k)) 1 (pow2 k);
  M.division_definition_lemma_1 t (pow2 k) (pow2 (n - k) - 1);
  let x = odd_preimage (n - k) u (t / pow2 k) in
  M.pow2_le_compat n (n - k);
  C.lemma_range x;
  lemma_scaled_product s f x;
  lemma_mul_value #(n - k) x u;
  M.lemma_div_exact t (pow2 k);
  x
#pop-options
