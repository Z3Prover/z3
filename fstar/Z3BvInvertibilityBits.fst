module Z3BvInvertibilityBits

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module M = FStar.Math.Lemmas

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_bitwise_sign (#n:pos) (a b:bv n)
  : Lemma
    (msb (bvand a b) == (msb a && msb b) /\
     msb (bvor a b) == (msb a || msb b)) =
  U.lemma_msb_pow2 a;
  U.lemma_msb_pow2 b;
  U.lemma_msb_pow2 (bvand a b);
  U.lemma_msb_pow2 (bvor a b);
  U.logand_definition a b 0;
  U.logor_definition a b 0

let lemma_clear_sign (#n:pos) (a:bv n)
  : Lemma (bvand a (signed_max n) == a % pow2 (n - 1)) =
  if n = 1 then U.logand_lemma_1 a
  else U.logand_mask a (n - 1)

let lemma_sign_mask (#n:pos) (a:bv n)
  : Lemma (bvand a (signed_min n) == (if msb a then signed_min n else 0)) =
  let high = signed_min n in
  let expected:bv n = if msb a then high else 0 in
  U.lemma_msb_pow2 a;
  (introduce forall (i:nat{i < n}).
    U.nth (bvand a high) i == U.nth expected i
  with (
    U.logand_definition a high i;
    U.pow2_nth_lemma #n (n - 1) i;
    U.zero_nth_lemma #n i
  ));
  U.nth_lemma (bvand a high) expected

let lemma_and_signed_bounds (#n:pos) (s x:bv n)
  : Lemma
    (to_int_signed (bvand (signed_min n) s) <= to_int_signed (bvand x s) /\
     to_int_signed (bvand x s) <= to_int_signed (bvand (signed_max n) s)) =
  let y = bvand x s in
  lemma_bitwise_sign x s;
  lemma_sign_mask s;
  U.logand_commutative (signed_min n) s;
  U.logand_commutative (signed_max n) s;
  lemma_clear_sign y;
  lemma_clear_sign s;
  U.logand_associative x s (signed_max n);
  U.logand_le x (bvand s (signed_max n));
  M.pow2_double_mult (n - 1);
  if not (msb y) then M.modulo_lemma y (pow2 (n - 1))

let lemma_complement_signed (#n:pos) (a:bv n)
  : Lemma (to_int_signed (bvnot a) == -1 - to_int_signed a) =
  U.lemma_lognot_value_mod a;
  M.pow2_double_mult (n - 1);
  if msb a then assert (not (msb (bvnot a)))
  else assert (msb (bvnot a))

let lemma_de_morgan (#n:pos) (a b:bv n)
  : Lemma (bvnot (bvor a b) == bvand (bvnot a) (bvnot b)) =
  let left = bvnot (bvor a b) in
  let right = bvand (bvnot a) (bvnot b) in
  (introduce forall (i:nat{i < n}). U.nth left i == U.nth right i
  with (
    U.lognot_definition (bvor a b) i;
    U.logor_definition a b i;
    U.logand_definition (bvnot a) (bvnot b) i;
    U.lognot_definition a i;
    U.lognot_definition b i
  ));
  U.nth_lemma left right

let lemma_or_signed_bounds (#n:pos) (s x:bv n)
  : Lemma
    (to_int_signed (bvor (signed_min n) s) <= to_int_signed (bvor x s) /\
     to_int_signed (bvor x s) <= to_int_signed (bvor (signed_max n) s)) =
  U.lemma_lognot_value_mod (signed_min n);
  U.lemma_lognot_value_mod (signed_max n);
  M.pow2_double_mult (n - 1);
  lemma_de_morgan x s;
  lemma_de_morgan (signed_min n) s;
  lemma_de_morgan (signed_max n) s;
  lemma_complement_signed (bvor x s);
  lemma_complement_signed (bvor (signed_min n) s);
  lemma_complement_signed (bvor (signed_max n) s);
  lemma_and_signed_bounds (bvnot s) (bvnot x)

let lemma_or_signed_max (#n:pos) (s:bv n)
  : Lemma
    (bvor (signed_max n) s == (if msb s then U.ones n else signed_max n)) =
  lemma_de_morgan (signed_max n) s;
  U.lemma_lognot_value_mod (signed_max n);
  U.lemma_lognot_value_mod s;
  U.logand_commutative (bvnot (signed_max n)) (bvnot s);
  lemma_sign_mask (bvnot s);
  U.lemma_lognot_value_mod (bvor (signed_max n) s);
  M.pow2_double_mult (n - 1)

let lemma_not_neg (#n:pos) (a:bv n)
  : Lemma (bvnot (bvneg a) == (if a = 0 then U.ones n else a - 1)) =
  U.lemma_lognot_value_mod (bvneg a);
  if a = 0 then M.modulo_lemma 0 (pow2 n)
  else (
    M.modulo_addition_lemma (-a) (pow2 n) 1;
    M.modulo_lemma (pow2 n - a) (pow2 n)
  )

let lemma_and_predecessor (#n:pos) (s t:bv n)
  : Lemma
    (to_int_signed (bvand (signed_min n) s) < to_int_signed t ==>
      to_int_signed (bvand (bvnot (bvneg t)) s) < to_int_signed t) =
  lemma_not_neg t;
  lemma_sign_mask s;
  U.logand_commutative (signed_min n) s;
  U.logand_le (bvnot (bvneg t)) s;
  lemma_bitwise_sign (bvnot (bvneg t)) s;
  M.pow2_double_mult (n - 1);
  if t = 0 then (
    U.logand_commutative (U.ones n) s;
    U.logand_lemma_2 s
  )
#pop-options
