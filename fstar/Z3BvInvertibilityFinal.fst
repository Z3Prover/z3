module Z3BvInvertibilityFinal

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module P = Z3BvInvertibilityProofs
module S = Z3BvInvertibilityShifts
module L = Z3BvInvertibilityLogical
module C = Z3BvInvertibilityCarry
module F = Z3BvInvertibilityFactors
module M = FStar.Math.Lemmas

#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let lemma_ashr_value (#n:pos) (a:bv n) (x:nat)
  : Lemma (bvashr a x ==
      (if msb a then bvnot (bvlshr (bvnot a) x) else bvlshr a x)) = ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let left_negative_witness (#n:pos) (s:bv n{s > 0})
  : Tot (x:bv n{bvshl s x == signed_min n}) =
  let (| k, u |) = F.factor n s in
  let x = n - 1 - k in
  P.lemma_width_fits n;
  assert_norm (signed_min n == pow2 (n - 1));
  U.shift_left_value_lemma s x;
  M.pow2_plus k x;
  M.pow2_double_mult (n - 1);
  M.paren_mul_right (pow2 k) u (pow2 x);
  M.swap_mul u (pow2 x);
  M.paren_mul_right (pow2 k) (pow2 x) u;
  M.swap_mul (pow2 (n - 1)) u;
  M.modulo_scale_lemma u (pow2 (n - 1)) 2;
  x

let lemma_left_lower_raw (#n:pos) (s t:bv n)
  : Lemma
    ((bvshl (signed_min n) s < bvadd t (signed_min n) <==>
       I.holds I.Slt (if s = 0 then 0 else signed_min n) t) /\
     (bvlshr t s < signed_min n <==>
       I.holds I.Sle (if s = 0 then 0 else signed_min n) t)) =
  assert_norm (signed_min n == pow2 (n - 1));
  M.pow2_double_mult (n - 1);
  U.shift_left_value_lemma (signed_min n) s;
  if s > 0 then (
    M.pow2_plus (n - 1) s;
    M.pow2_multiplication_modulo_lemma_1 1 n (n - 1 + s);
    S.lemma_right_positive t s
  )
  else (
    assert (s == 0);
    U.lemma_uint_mod (signed_min n);
    S.lemma_right_endpoints t
  );
  if t < signed_min n then M.modulo_lemma (t + signed_min n) (pow2 n)
  else (
    M.modulo_addition_lemma (t - signed_min n) (pow2 n) 1;
    M.modulo_lemma (t - signed_min n) (pow2 n)
  )

let lemma_ashr_projection (#n:pos) (s:bv n{s < n}) (x:bv n)
  : Lemma (bvashr (bvshl (bvashr x s) s) s == bvashr x s) =
  L.lemma_signed_constants n;
  M.pow2_double_mult (n - 1);
  M.pow2_plus (n - 1 - s) s;
  M.pow2_le_compat (n - 1) s;
  C.lemma_range x;
  U.lemma_lognot_value_mod x;
  lemma_ashr_value x s;
  let y = bvashr x s in
  U.shift_left_value_lemma y s;
  if not (msb x) then (
    U.shift_right_value_lemma x s;
    M.division_propriety x (pow2 s);
    M.modulo_lemma (y * pow2 s) (pow2 n);
    L.lemma_right_projection s x;
    lemma_ashr_value (bvshl y s) s
  )
  else (
    let q = bvlshr (bvnot x) s in
    U.lemma_lognot_value_mod q;
    U.shift_right_value_lemma (bvnot x) s;
    M.distributivity_sub_left (pow2 (n - 1 - s)) 1 (pow2 s);
    M.division_definition_lemma_1 (bvnot x) (pow2 s) (pow2 (n - 1 - s) - 1);
    M.lemma_mult_le_left (pow2 s) (q + 1) (pow2 (n - 1 - s));
    M.distributivity_sub_left (pow2 n) (q + 1) (pow2 s);
    M.modulo_addition_lemma (-(q + 1) * pow2 s) (pow2 n) (pow2 s);
    M.modulo_addition_lemma (-(q + 1) * pow2 s) (pow2 n) 1;
    let v = pow2 n - (q + 1) * pow2 s in
    M.modulo_lemma v (pow2 n);
    assert (bvshl y s == v);
    U.lemma_lognot_value_mod (bvshl y s);
    U.shift_right_value_lemma (bvnot (bvshl y s)) s;
    M.distributivity_add_left q 1 (pow2 s);
    M.division_definition ((q + 1) * pow2 s - 1) (pow2 s) q;
    lemma_ashr_value (bvshl y s) s
  )
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_left_amount_signed (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sle}) (s t:bv n)
  : Lemma (condition ShiftLeftAmount r s t <==>
      (exists (x:bv n). I.holds r (apply ShiftLeftAmount s x) t)) =
  lemma_left_lower_raw s t;
  let x:bv n = if s > 0 then left_negative_witness s else 0 in
  U.shift_left_value_lemma #n 0 0;
  assert (condition ShiftLeftAmount r s t ==>
    I.holds r (apply ShiftLeftAmount s x) t);
  introduce forall x.
    to_int_signed (if s = 0 then 0 else signed_min n) <=
      to_int_signed (apply ShiftLeftAmount s x)
  with (
    M.pow2_double_mult (n - 1);
    if s = 0 then U.shift_left_value_lemma s x
  )

let lemma_ashr_eq (#n:pos) (s t:bv n)
  : Lemma (condition ArithmeticRightValue I.Eq s t <==>
      (exists (x:bv n). I.holds I.Eq (apply ArithmeticRightValue s x) t)) =
  P.lemma_width_fits n;
  U.lemma_uint_mod #n n;
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  let x = if s < n then bvshl t s else t in
  if s >= n then (
    I.lemma_ashr_large t s;
    P.lemma_ashr_ones s;
    P.lemma_zero_attained ArithmeticRightValue s
  );
  assert (condition ArithmeticRightValue I.Eq s t ==>
    I.holds I.Eq (apply ArithmeticRightValue s x) t);
  introduce forall x. I.holds I.Eq (apply ArithmeticRightValue s x) t ==>
    condition ArithmeticRightValue I.Eq s t
  with (
    if s < n then lemma_ashr_projection s x
    else I.lemma_ashr_large x s
  )
#pop-options
