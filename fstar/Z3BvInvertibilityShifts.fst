module Z3BvInvertibilityShifts

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module P = Z3BvInvertibilityProofs
module B = Z3BvInvertibilityBits
module M = FStar.Math.Lemmas

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_right_bound (#n:pos) (a:bv n) (x:nat)
  : Lemma (bvlshr a x <= a) =
  U.shift_right_value_lemma a x;
  M.division_propriety a (pow2 x);
  M.lemma_mult_le_left (a / pow2 x) 1 (pow2 x)

let lemma_right_monotone (#n:pos) (a b:bv n{a <= b}) (x:nat)
  : Lemma (bvlshr a x <= bvlshr b x) =
  U.shift_right_value_lemma a x;
  U.shift_right_value_lemma b x;
  M.lemma_div_le a b (pow2 x)

let lemma_right_positive (#n:pos) (a:bv n) (x:pos)
  : Lemma (bvlshr a x < signed_min n /\ bvlshr a x <= bvlshr a 1) =
  U.shift_right_value_lemma a x;
  U.shift_right_value_lemma a 1;
  M.pow2_le_compat x 1;
  M.pow2_double_mult (n - 1);
  M.division_propriety a (pow2 x);
  M.lemma_mult_le_left (a / pow2 x) 2 (pow2 x);
  M.division_definition_lemma_2 a 2 (a / pow2 x)

let lemma_right_endpoints (#n:pos) (s:bv n)
  : Lemma (bvlshr s 0 == s /\ bvlshr s n == 0) =
  U.shift_right_value_lemma s 0;
  U.shift_right_value_lemma s n;
  M.small_div s (pow2 n)

let right_signed_upper (#n:pos) (s:bv n) : bv n =
  if msb s then bvlshr s 1 else s

let right_upper_witness (#n:pos) (s:bv n) : bv n =
  if msb s then 1 else 0

let lemma_right_signed_bounds (#n:pos) (s:bv n) (x:nat)
  : Lemma
    ((if msb s then to_int_signed s else 0) <= to_int_signed (bvlshr s x) /\
     to_int_signed (bvlshr s x) <= to_int_signed (right_signed_upper s)) =
  lemma_right_bound s x;
  lemma_right_bound s 1;
  lemma_right_positive s 1;
  lemma_right_endpoints s;
  if x > 0 then lemma_right_positive s x

let lemma_right_amount_unsigned (#n:pos)
  (r:I.relation{r = I.Ugt \/ r = I.Uge}) (s t:bv n)
  : Lemma (condition ShiftRightAmount r s t <==>
      (exists (x:bv n). I.holds r (apply ShiftRightAmount s x) t)) =
  lemma_right_endpoints s;
  assert (condition ShiftRightAmount r s t ==>
    I.holds r (apply ShiftRightAmount s 0) t);
  introduce forall x. apply ShiftRightAmount s x <= s
  with lemma_right_bound s x

let lemma_right_amount_signed_lower (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sle}) (s t:bv n)
  : Lemma (condition ShiftRightAmount r s t <==>
      (exists (x:bv n). I.holds r (apply ShiftRightAmount s x) t)) =
  P.lemma_width_fits n;
  U.lemma_uint_mod #n 0;
  lemma_right_endpoints s;
  let x:bv n = if msb s then 0 else n in
  assert (condition ShiftRightAmount r s t ==>
    I.holds r (apply ShiftRightAmount s x) t);
  introduce forall x.
    (if msb s then to_int_signed s else 0) <= to_int_signed (bvlshr s x)
  with lemma_right_signed_bounds s x

let lemma_right_amount_signed_upper (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition ShiftRightAmount r s t <==>
      (exists (x:bv n). I.holds r (apply ShiftRightAmount s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lemma_one_mod_pow2 #n;
  lemma_right_endpoints s;
  let x = right_upper_witness s in
  assert (apply ShiftRightAmount s x == right_signed_upper s);
  assert (condition ShiftRightAmount r s t <==>
    I.holds r (right_signed_upper s) t);
  assert (condition ShiftRightAmount r s t ==>
    I.holds r (apply ShiftRightAmount s x) t);
  introduce forall x.
    to_int_signed (bvlshr s x) <= to_int_signed (right_signed_upper s)
  with lemma_right_signed_bounds s x

let lemma_ashr_bounds (#n:pos) (s:bv n) (x:nat)
  : Lemma
    ((if msb s then s else 0) <= bvashr s x /\
     bvashr s x <= (if msb s then U.ones n else s) /\
     msb (bvashr s x) == msb s /\
     (if msb s then to_int_signed s else 0) <= to_int_signed (bvashr s x) /\
     to_int_signed (bvashr s x) <= (if msb s then -1 else to_int_signed s)) =
  M.pow2_double_mult (n - 1);
  U.lemma_lognot_value_mod s;
  U.lemma_lognot_value_mod (bvlshr (bvnot s) x);
  lemma_right_bound s x;
  lemma_right_bound (bvnot s) x

let lemma_ashr_amount_endpoints (#n:pos) (s:bv n)
  : Lemma
    (bvashr s 0 == s /\
     bvashr s n == (if msb s then U.ones n else 0)) =
  Z3BvRewriter.lemma_bvashr_zero s;
  I.lemma_ashr_large s n

let lemma_ashr_amount_neq (#n:pos) (s t:bv n)
  : Lemma (condition ArithmeticRightAmount I.Ne s t <==>
      (exists (x:bv n). I.holds I.Ne (apply ArithmeticRightAmount s x) t)) =
  P.lemma_width_fits n;
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  lemma_ashr_amount_endpoints s;
  M.pow2_double_mult (n - 1);
  let x:bv n = if s <> t then 0 else n in
  assert (condition ArithmeticRightAmount I.Ne s t ==>
    I.holds I.Ne (apply ArithmeticRightAmount s x) t);
  introduce forall (x:bv n).
    (s == 0 ==> bvashr s x == 0) /\
    (s == U.ones n ==> bvashr s x == U.ones n)
  with (
    if s = 0 then P.lemma_zero_attained ArithmeticRightValue x
    else if s = U.ones n then P.lemma_ashr_ones x
  )

let lemma_ashr_amount_ugt_condition (#n:pos) (s t:bv n)
  : Lemma (condition ArithmeticRightAmount I.Ugt s t <==>
      t < (if msb s then U.ones n else s)) =
  U.lemma_lognot_value_mod t;
  M.pow2_double_mult (n - 1);
  lemma_right_bound s (bvnot t);
  lemma_right_endpoints s;
  if t < U.ones n then lemma_right_positive s (bvnot t)

let lemma_ashr_amount_unsigned (#n:pos)
  (r:I.relation{r = I.Ult \/ r = I.Ugt \/ r = I.Ule \/ r = I.Uge}) (s t:bv n)
  : Lemma (condition ArithmeticRightAmount r s t <==>
      (exists (x:bv n). I.holds r (apply ArithmeticRightAmount s x) t)) =
  P.lemma_width_fits n;
  U.lemma_uint_mod #n 0;
  U.lemma_lognot_value_mod s;
  M.pow2_double_mult (n - 1);
  lemma_ashr_amount_endpoints s;
  lemma_ashr_amount_ugt_condition s t;
  let x:bv n =
    if r = I.Ult || r = I.Ule then (if msb s then 0 else n)
    else (if msb s then n else 0) in
  assert (condition ArithmeticRightAmount r s t ==>
    I.holds r (apply ArithmeticRightAmount s x) t);
  introduce forall x.
    (if msb s then s else 0) <= bvashr s x /\
    bvashr s x <= (if msb s then U.ones n else s)
  with lemma_ashr_bounds s x

let lemma_ashr_amount_signed_lower (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sle}) (s t:bv n)
  : Lemma (condition ArithmeticRightAmount r s t <==>
      (exists (x:bv n). I.holds r (apply ArithmeticRightAmount s x) t)) =
  P.lemma_width_fits n;
  U.lemma_uint_mod #n 0;
  lemma_ashr_amount_endpoints s;
  let x:bv n = if msb s then 0 else n in
  assert (condition ArithmeticRightAmount r s t ==>
    I.holds r (apply ArithmeticRightAmount s x) t);
  introduce forall x.
    (if msb s then to_int_signed s else 0) <= to_int_signed (bvashr s x)
  with lemma_ashr_bounds s x

#push-options "--fuel 1 --ifuel 1"
let lemma_ashr_amount_signed_upper_raw (#n:pos) (s t:bv n)
  : Lemma
    ((I.holds I.Slt t (bvand s (signed_max n)) &&
       I.holds I.Slt t (bvor s (signed_max n)) <==>
       (if msb s then -1 else to_int_signed s) > to_int_signed t) /\
     (not (t < bvnot t && I.holds I.Slt s t) <==>
       (if msb s then -1 else to_int_signed s) >= to_int_signed t)) =
  U.lemma_uint_mod #n 0;
  U.lemma_lognot_value_mod t;
  assert (U.ones n == pow2 n - 1);
  M.pow2_double_mult (n - 1);
  B.lemma_clear_sign s;
  U.logor_commutative s (signed_max n);
  B.lemma_or_signed_max s;
  if msb s then (
    M.modulo_addition_lemma (s - signed_min n) (signed_min n) 1;
    M.modulo_lemma (s - signed_min n) (signed_min n)
  )
  else M.modulo_lemma s (signed_min n)
#pop-options

let lemma_ashr_amount_signed_upper_condition (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition ArithmeticRightAmount r s t <==>
      (if msb s then -1 else to_int_signed s) > to_int_signed t \/ r == I.Sge /\
      (if msb s then -1 else to_int_signed s) == to_int_signed t) =
  lemma_ashr_amount_signed_upper_raw s t;
  match r with
  | I.Sgt | I.Sge -> ()

let lemma_ashr_amount_signed_upper (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition ArithmeticRightAmount r s t <==>
      (exists (x:bv n). I.holds r (apply ArithmeticRightAmount s x) t)) =
  P.lemma_width_fits n;
  lemma_ashr_amount_endpoints s;
  lemma_ashr_amount_signed_upper_condition r s t;
  let x:bv n = if msb s then n else 0 in
  assert (condition ArithmeticRightAmount r s t ==>
    I.holds r (apply ArithmeticRightAmount s x) t);
  introduce forall x.
    to_int_signed (bvashr s x) <= (if msb s then -1 else to_int_signed s)
  with lemma_ashr_bounds s x

let lemma_ashr_value_extrema (#n:pos) (s x:bv n)
  : Lemma
    (bvashr (signed_min n) s == bvnot (bvlshr (signed_max n) s) /\
     bvashr (signed_max n) s == bvlshr (signed_max n) s /\
     to_int_signed (bvashr (signed_min n) s) <= to_int_signed (bvashr x s) /\
     to_int_signed (bvashr x s) <= to_int_signed (bvlshr (signed_max n) s)) =
  M.pow2_double_mult (n - 1);
  U.lemma_lognot_value_mod (signed_min n);
  U.lemma_lognot_value_mod x;
  U.lemma_lognot_value_mod (bvlshr (bvnot x) s);
  U.lemma_lognot_value_mod (bvlshr (signed_max n) s);
  lemma_right_bound (signed_max n) s;
  if msb x then (
    lemma_right_monotone (bvnot x) (signed_max n) s;
    lemma_right_bound (bvnot x) s
  )
  else (
    lemma_right_monotone x (signed_max n) s;
    lemma_right_bound x s
  )

let lemma_ashr_value_signed (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sgt \/ r = I.Sle \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition ArithmeticRightValue r s t <==>
      (exists (x:bv n). I.holds r (apply ArithmeticRightValue s x) t)) =
  lemma_ashr_value_extrema s 0;
  let x = if r = I.Slt || r = I.Sle then signed_min n else signed_max n in
  assert (condition ArithmeticRightValue r s t ==>
    I.holds r (apply ArithmeticRightValue s x) t);
  introduce forall x.
    to_int_signed (bvashr (signed_min n) s) <= to_int_signed (bvashr x s) /\
    to_int_signed (bvashr x s) <= to_int_signed (bvlshr (signed_max n) s)
  with lemma_ashr_value_extrema s x
#pop-options
