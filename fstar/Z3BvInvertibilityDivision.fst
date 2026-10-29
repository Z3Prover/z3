module Z3BvInvertibilityDivision

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module P = Z3BvInvertibilityProofs
module B = Z3BvInvertibilityBits
module M = FStar.Math.Lemmas

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_divisor_proper (#n:pos) (s:bv n) (x:bv n{x >= 2})
  : Lemma
    (apply Divisor s x < signed_min n /\
     apply Divisor s x <= s / 2 /\
     apply Divisor s x <= s) =
  M.pow2_double_mult (n - 1);
  M.division_propriety s x;
  M.lemma_mult_le_left (s / x) 2 x;
  M.division_definition_lemma_2 s 2 (s / x);
  M.lemma_div_le s (2 * s) 2

let divisor_signed_upper (#n:pos) (s:bv n) : bv n =
  if n = 1 || not (msb s) then s else bvlshr s 1

let divisor_signed_witness (#n:pos) (s:bv n) : bv n =
  if n = 1 || not (msb s) then 1
  else (P.lemma_width_fits n; 2)

let lemma_divisor_signed_bounds (#n:pos) (s x:bv n)
  : Lemma
    (let y = apply Divisor s x in
     (if msb s then to_int_signed s else -1) <= to_int_signed y /\
     to_int_signed y <= to_int_signed (divisor_signed_upper s)) =
  if x >= 2 then (
    lemma_divisor_proper s x;
    M.pow2_double_mult (n - 1);
    U.shift_right_value_lemma s 1
  )
  else (
    assert (x == 0 \/ x == 1);
    P.lemma_division_endpoints s;
    U.lognot_lemma_1 #n;
    M.pow2_double_mult (n - 1);
    U.shift_right_value_lemma s 1
  )

let lemma_divisor_signed_upper_attained (#n:pos) (s:bv n)
  : Lemma
    (apply Divisor s (divisor_signed_witness s) == divisor_signed_upper s) =
  P.lemma_division_endpoints s;
  U.shift_right_value_lemma s 1

let lemma_divisor_signed_lower (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sle}) (s t:bv n)
  : Lemma (condition Divisor r s t <==>
      (exists (x:bv n). I.holds r (apply Divisor s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  M.pow2_double_mult (n - 1);
  P.lemma_division_endpoints s;
  let x:bv n = if msb s then 1 else 0 in
  assert (condition Divisor r s t ==>
    I.holds r (apply Divisor s x) t);
  introduce forall x.
    (if msb s then to_int_signed s else -1) <=
      to_int_signed (apply Divisor s x)
  with lemma_divisor_signed_bounds s x

let lemma_divisor_signed_upper (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition Divisor r s t <==>
      (exists (x:bv n). I.holds r (apply Divisor s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lemma_one_mod_pow2 #n;
  lemma_divisor_signed_upper_attained s;
  let x = divisor_signed_witness s in
  assert (condition Divisor r s t ==>
    I.holds r (apply Divisor s x) t);
  assert (condition Divisor r s t <==>
    I.holds r (divisor_signed_upper s) t);
  introduce forall x.
    to_int_signed (apply Divisor s x) <=
      to_int_signed (divisor_signed_upper s)
  with lemma_divisor_signed_bounds s x

let lemma_divisor_neq (#n:pos) (s t:bv n)
  : Lemma (condition Divisor I.Ne s t <==>
      (exists (x:bv n). I.holds I.Ne (apply Divisor s x) t)) =
  P.lemma_division_endpoints s;
  U.lognot_lemma_1 #n;
  U.logand_lemma_1 s;
  U.logand_self #n 1;
  if n = 1 then (
    let x:bv n = if t <> 1 then 0 else 1 in
    assert (condition Divisor I.Ne s t ==>
      I.holds I.Ne (apply Divisor s x) t);
    introduce forall x. s = 1 ==> apply Divisor s x == 1
    with (if x > 0 then assert (x == 1))
  )
  else (
    P.lemma_width_fits n;
    lemma_divisor_proper s 2;
    let x:bv n = if t <> U.ones n then 0 else if s <> t then 1 else 2 in
    assert (I.holds I.Ne (apply Divisor s x) t)
  )

let lemma_divisor_minimum (#n:pos) (s x:bv n)
  : Lemma
    ((if s = U.ones n then 1 else 0) <= apply Divisor s x /\
     apply Divisor s (U.ones n) == (if s = U.ones n then 1 else 0)) =
  if s < U.ones n then M.small_div s (U.ones n)
  else (
    assert (s == U.ones n);
    M.cancel_mul_div 1 s;
    if x > 0 then M.division_definition_lemma_2 s x 1
  )

#push-options "--fuel 1 --ifuel 1"
let lemma_divisor_small_raw (#n:pos) (s t:bv n)
  : Lemma
    ((0 < bvnot (bvand (bvneg t) s) && 0 < t <==>
       (if s = U.ones n then 1 else 0) < t) /\
     (0 < bvor (bvnot s) t <==>
       (if s = U.ones n then 1 else 0) <= t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  U.lemma_lognot_value_mod s;
  U.logor_ge (bvnot s) t;
  U.logand_le (bvneg t) s;
  U.lemma_lognot_value_mod (bvand (bvneg t) s);
  U.lemma_lognot_value_mod (bvneg t);
  B.lemma_not_neg t;
  assert (U.ones n == pow2 n - 1);
  assert (s <= U.ones n);
  if t < 1 then (
    assert (t == 0);
    U.logor_lemma_1 (bvnot s)
  )
  else if t < 2 then (
    assert (t == 1);
    U.lemma_lognot_value_mod #n 0;
    B.lemma_not_neg #n 1;
    assert (bvneg t == U.ones n);
    U.logand_commutative (U.ones n) s;
    U.logand_lemma_2 s;
    assert (bvand (bvneg t) s == s)
  )
  else (
    assert (t >= 2);
    assert (bvneg t < U.ones n);
    assert (bvnot (bvand (bvneg t) s) > 0);
    assert (0 < bvnot (bvand (bvneg t) s) && 0 < bvor (bvnot s) t)
  )
#pop-options

let lemma_divisor_small_conditions (#n:pos) (s t:bv n)
  : Lemma
    ((condition Divisor I.Ult s t <==>
       (if s = U.ones n then 1 else 0) < t) /\
     (condition Divisor I.Ule s t <==>
       (if s = U.ones n then 1 else 0) <= t)) =
  U.lemma_uint_mod #n 0;
  lemma_divisor_small_raw s t

let lemma_divisor_small (#n:pos)
  (r:I.relation{r = I.Ult \/ r = I.Ule}) (s t:bv n)
  : Lemma (condition Divisor r s t <==>
      (exists (x:bv n). I.holds r (apply Divisor s x) t)) =
  lemma_divisor_small_conditions s t;
  lemma_divisor_minimum s 0;
  assert (condition Divisor r s t ==>
    I.holds r (apply Divisor s (U.ones n)) t);
  introduce forall x.
    (if s = U.ones n then 1 else 0) <= apply Divisor s x
  with lemma_divisor_minimum s x

let lemma_divisor_involution (#n:pos) (s x:bv n)
  : Lemma
    (let t = apply Divisor s x in apply Divisor s (bvudiv s t) == t) =
  P.lemma_division_endpoints s;
  if x = 0 then (
    lemma_divisor_minimum s 0;
    if s = U.ones n then () else M.small_div s (U.ones n)
  )
  else (
    let t = apply Divisor s x in
    if t = 0 then (
      M.division_propriety s x;
      M.small_div s (U.ones n)
    )
    else (
      M.division_propriety s x;
      M.division_propriety s t;
      M.division_definition_lemma_2 s t x;
      let q = s / t in
      M.lemma_mult_le_left (t + 1) x q;
      M.division_definition s q t
    )
  )

let lemma_divisor_eq (#n:pos) (s t:bv n)
  : Lemma (condition Divisor I.Eq s t <==>
      (exists (x:bv n). I.holds I.Eq (apply Divisor s x) t)) =
  let x = bvudiv s t in
  assert (condition Divisor I.Eq s t ==> I.holds I.Eq (apply Divisor s x) t);
  introduce forall x. I.holds I.Eq (apply Divisor s x) t ==>
    condition Divisor I.Eq s t
  with lemma_divisor_involution s x
#pop-options
