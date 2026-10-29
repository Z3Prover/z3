module Z3BvInvertibilityLogical

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module P = Z3BvInvertibilityProofs
module B = Z3BvInvertibilityBits
module S = Z3BvInvertibilityShifts
module M = FStar.Math.Lemmas

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_signed_constants (n:pos)
  : Lemma (signed_min n == pow2 (n - 1) /\ signed_max n == pow2 (n - 1) - 1) =
  assert_norm (signed_min n == pow2 (n - 1));
  assert_norm (signed_max n == pow2 (n - 1) - 1)

let lemma_left_value (#n:pos) (s x:bv n)
  : Lemma (bvshl x s ==
      (if s < n then (x % pow2 (n - s)) * pow2 s else 0)) =
  U.shift_left_value_lemma x s;
  if s < n then M.pow2_multiplication_modulo_lemma_2 x n s
  else M.pow2_multiplication_modulo_lemma_1 x n s

let lemma_left_right (#n:pos) (s x:bv n)
  : Lemma (bvlshr (bvshl x s) s ==
      (if s < n then x % pow2 (n - s) else 0)) =
  lemma_left_value s x;
  U.shift_right_value_lemma (bvshl x s) s;
  if s < n then M.cancel_mul_div (x % pow2 (n - s)) (pow2 s)
  else M.small_div 0 (pow2 s)

let lemma_left_projection (#n:pos) (s x:bv n)
  : Lemma (bvshl (bvlshr (bvshl x s) s) s == bvshl x s) =
  lemma_left_right s x;
  lemma_left_value s x;
  lemma_left_value s (bvlshr (bvshl x s) s);
  if s < n then M.modulo_lemma (x % pow2 (n - s)) (pow2 (n - s))

let lemma_right_projection (#n:pos) (s x:bv n)
  : Lemma (bvlshr (bvshl (bvlshr x s) s) s == bvlshr x s) =
  U.shift_right_value_lemma x s;
  M.division_propriety x (pow2 s);
  let y = bvlshr x s in
  M.modulo_lemma (y * pow2 s) (pow2 n);
  U.shift_left_value_lemma y s;
  U.shift_right_value_lemma (bvshl y s) s;
  M.cancel_mul_div y (pow2 s)

let lemma_logical_eq (#n:pos) (op:P.logical_value_operator) (s t:bv n)
  : Lemma (condition op I.Eq s t <==>
      (exists (x:bv n). I.holds I.Eq (apply op s x) t)) =
  let x = if op = ShiftLeftValue then bvlshr t s else bvshl t s in
  assert (condition op I.Eq s t ==> I.holds I.Eq (apply op s x) t);
  introduce forall x. I.holds I.Eq (apply op s x) t ==> condition op I.Eq s t
  with (
    match op with
    | ShiftLeftValue -> lemma_left_projection s x
    | ShiftRightValue -> lemma_right_projection s x
  )

#push-options "--fuel 1 --ifuel 1"
let lemma_maxima (#n:pos) (s:bv n)
  : Lemma
    (bvshl (U.ones n) s == (if s < n then pow2 n - pow2 s else 0) /\
     bvlshr (U.ones n) s == (if s < n then pow2 (n - s) - 1 else 0) /\
     bvlshr (bvnot s) s == bvlshr (U.ones n) s) =
  lemma_left_value s (U.ones n);
  U.shift_right_value_lemma (U.ones n) s;
  U.shift_right_value_lemma (bvnot s) s;
  U.lemma_lognot_value_mod s;
  U.lognot_lemma_1 #n;
  U.lemma_lognot_value_mod #n 0;
  assert (U.ones n == pow2 n - 1);
  if s < n then (
    M.pow2_plus (n - s) s;
    M.distributivity_sub_left (pow2 (n - s)) 1 (pow2 s);
    M.distributivity_sub_left (pow2 s) 1 (pow2 (n - s));
    assert ((pow2 (n - s) - 1) * pow2 s == pow2 n - pow2 s);
    M.modulo_addition_lemma (pow2 (n - s) - 1) (pow2 (n - s)) (pow2 s - 1);
    M.modulo_lemma (pow2 (n - s) - 1) (pow2 (n - s));
    if s > 0 then P.lemma_width_fits s;
    assert (s < pow2 s);
    M.division_definition (U.ones n) (pow2 s) (pow2 (n - s) - 1);
    M.division_definition (bvnot s) (pow2 s) (pow2 (n - s) - 1)
  )
  else (
    M.pow2_le_compat s n;
    M.small_div (U.ones n) (pow2 s);
    M.small_div (bvnot s) (pow2 s)
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
let lemma_logical_max (#n:pos) (op:P.logical_value_operator) (s x:bv n)
  : Lemma (apply op s x <= apply op s (U.ones n)) =
  lemma_maxima s;
  match op with
  | ShiftRightValue -> S.lemma_right_monotone x (U.ones n) s
  | ShiftLeftValue ->
    lemma_left_value s x;
    if s < n then (
      M.pow2_plus (n - s) s;
      M.distributivity_sub_right (pow2 s) (pow2 (n - s)) 1;
      M.lemma_mult_le_left (pow2 s) (x % pow2 (n - s)) (pow2 (n - s) - 1)
    )
#pop-options

let lemma_logical_ugt (#n:pos) (op:P.logical_value_operator) (s t:bv n)
  : Lemma (condition op I.Ugt s t <==>
      (exists (x:bv n). I.holds I.Ugt (apply op s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  lemma_maxima s;
  assert (condition op I.Ugt s t ==>
    I.holds I.Ugt (apply op s (U.ones n)) t);
  introduce forall x. apply op s x <= apply op s (U.ones n)
  with lemma_logical_max op s x

let lemma_left_uge (#n:pos) (s t:bv n)
  : Lemma (condition ShiftLeftValue I.Uge s t <==>
      (exists (x:bv n). I.holds I.Uge (apply ShiftLeftValue s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  assert (condition ShiftLeftValue I.Uge s t ==>
    I.holds I.Uge (apply ShiftLeftValue s (U.ones n)) t);
  introduce forall x. apply ShiftLeftValue s x <= apply ShiftLeftValue s (U.ones n)
  with lemma_logical_max ShiftLeftValue s x

let lemma_right_reachable (#n:pos) (s t:bv n{t <= bvlshr (U.ones n) s})
  : Lemma (bvlshr (bvshl t s) s == t) =
  lemma_maxima s;
  lemma_left_right s t;
  if s < n then M.modulo_lemma t (pow2 (n - s))

let lemma_right_uge (#n:pos) (s t:bv n)
  : Lemma (condition ShiftRightValue I.Uge s t <==>
      (exists (x:bv n). I.holds I.Uge (apply ShiftRightValue s x) t)) =
  let x = bvshl t s in
  assert (condition ShiftRightValue I.Uge s t ==>
    I.holds I.Uge (apply ShiftRightValue s x) t);
  introduce forall x. I.holds I.Uge (apply ShiftRightValue s x) t ==>
    condition ShiftRightValue I.Uge s t
  with (
    lemma_logical_max ShiftRightValue s x;
    if t <= bvlshr (U.ones n) s then lemma_right_reachable s t
  )

let right_lower (#n:pos) (s:bv n) : bv n =
  if s = 0 then signed_min n else 0

let right_upper (#n:pos) (s:bv n) : bv n =
  if s = 0 then signed_max n else bvlshr (U.ones n) s

let lemma_right_signed_bounds (#n:pos) (s x:bv n)
  : Lemma
    (to_int_signed (right_lower s) <= to_int_signed (bvlshr x s) /\
     to_int_signed (bvlshr x s) <= to_int_signed (right_upper s)) =
  M.pow2_double_mult (n - 1);
  if s > 0 then (
    S.lemma_right_positive x s;
    S.lemma_right_positive (U.ones n) s;
    lemma_logical_max ShiftRightValue s x
  )
  else S.lemma_right_endpoints x

#push-options "--fuel 0 --ifuel 0"
let lemma_power_mask_remainder (a b:nat)
  : Lemma ((pow2 (a + b) - 1) % pow2 a == pow2 a - 1) =
  M.pow2_plus a b;
  M.swap_mul (pow2 a) (pow2 b);
  M.distributivity_sub_left (pow2 b) 1 (pow2 a);
  M.swap_mul (pow2 b - 1) (pow2 a);
  assert (pow2 (a + b) - 1 ==
    pow2 a - 1 + pow2 a * (pow2 b - 1));
  M.modulo_addition_lemma (pow2 a - 1) (pow2 a) (pow2 b - 1);
  M.modulo_lemma (pow2 a - 1) (pow2 a)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let lemma_right_upper_attained (#n:pos) (s:bv n)
  : Lemma
    (bvlshr (bvshl (signed_max n) s) s == right_upper s) =
  lemma_signed_constants n;
  U.lemma_uint_mod (signed_max n);
  lemma_left_right s (signed_max n);
  lemma_maxima s;
  M.pow2_double_mult (n - 1);
  if s > 0 && s < n then (
    lemma_power_mask_remainder (n - s) (s - 1)
  )
  else if s = 0 then S.lemma_right_endpoints (signed_max n)
#pop-options

let lemma_right_lower_condition (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sle}) (s t:bv n)
  : Lemma (condition ShiftRightValue r s t <==>
      I.holds r (right_lower s) t) =
  B.lemma_not_neg t;
  S.lemma_right_bound t s;
  M.pow2_double_mult (n - 1);
  if s > 0 then (
    S.lemma_right_positive t s;
    S.lemma_right_positive (bvnot (bvneg t)) s;
    S.lemma_right_bound (bvnot (bvneg t)) s
  )
  else (
    S.lemma_right_endpoints t;
    S.lemma_right_endpoints (bvnot (bvneg t))
  )

let lemma_right_signed_lower (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sle}) (s t:bv n)
  : Lemma (condition ShiftRightValue r s t <==>
      (exists (x:bv n). I.holds r (apply ShiftRightValue s x) t)) =
  lemma_right_lower_condition r s t;
  S.lemma_right_endpoints (signed_min n);
  U.shift_right_value_lemma #n 0 s;
  M.small_div 0 (pow2 s);
  let x:bv n = if s = 0 then signed_min n else 0 in
  assert (bvlshr x s == right_lower s);
  assert (condition ShiftRightValue r s t ==>
    I.holds r (apply ShiftRightValue s x) t);
  introduce forall x.
    to_int_signed (right_lower s) <= to_int_signed (bvlshr x s)
  with lemma_right_signed_bounds s x

let lemma_right_signed_upper (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition ShiftRightValue r s t <==>
      (exists (x:bv n). I.holds r (apply ShiftRightValue s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  lemma_right_upper_attained s;
  lemma_right_signed_bounds s (U.ones n);
  let x = bvshl (signed_max n) s in
  assert (condition ShiftRightValue r s t <==> I.holds r (right_upper s) t);
  assert (condition ShiftRightValue r s t ==>
    I.holds r (apply ShiftRightValue s x) t);
  introduce forall x.
    to_int_signed (bvlshr x s) <= to_int_signed (right_upper s)
  with lemma_right_signed_bounds s x

let left_lower (#n:pos) (s:bv n) : bv n =
  if s < n then signed_min n else 0

let left_upper (#n:pos) (s:bv n) : bv n =
  if s < n then (
    lemma_signed_constants n;
    M.pow2_le_compat (n - 1) s;
    signed_min n - pow2 s
  )
  else 0

let left_lower_witness (#n:pos) (s:bv n) : bv n =
  if s < n then U.pow2_n #n (n - 1 - s) else 0

let left_upper_witness (#n:pos) (s:bv n) : bv n =
  if s < n then U.pow2_n #n (n - 1 - s) - 1 else 0

#push-options "--fuel 1 --ifuel 1"
let lemma_left_signed_endpoints (#n:pos) (s:bv n)
  : Lemma
    (bvshl (left_lower_witness s) s == left_lower s /\
     bvshl (left_upper_witness s) s == left_upper s /\
     bvshl (bvlshr (signed_min n) s) s == left_lower s /\
     bvand (bvshl (signed_max n) s) (signed_max n) == left_upper s) =
  lemma_signed_constants n;
  assert_norm (left_lower_witness s ==
    (if s < n then pow2 (n - 1 - s) else 0));
  assert_norm (left_upper_witness s ==
    (if s < n then pow2 (n - 1 - s) - 1 else 0));
  lemma_left_value s (left_lower_witness s);
  lemma_left_value s (left_upper_witness s);
  lemma_left_value s (signed_max n);
  U.shift_right_value_lemma (signed_min n) s;
  B.lemma_clear_sign (bvshl (signed_max n) s);
  M.pow2_double_mult (n - 1);
  if s < n then (
    M.pow2_le_compat (n - 1) s;
    M.pow2_plus (n - 1 - s) s;
    M.distributivity_sub_left (pow2 (n - 1 - s)) 1 (pow2 s);
    M.pow2_double_mult (n - 1 - s);
    M.modulo_lemma (left_lower_witness s) (pow2 (n - s));
    M.modulo_lemma (left_upper_witness s) (pow2 (n - s));
    M.cancel_mul_div (pow2 (n - 1 - s)) (pow2 s);
    lemma_left_value s (bvlshr (signed_min n) s);
    if s > 0 then (
      M.pow2_plus (n - s) s;
      M.distributivity_sub_left (pow2 (n - s)) 1 (pow2 s);
      M.pow2_plus (n - s) (s - 1);
      M.swap_mul (pow2 (n - s)) (pow2 (s - 1));
      M.distributivity_sub_left (pow2 (s - 1)) 1 (pow2 (n - s));
      M.modulo_addition_lemma (pow2 (n - s) - 1) (pow2 (n - s)) (pow2 (s - 1) - 1);
      M.modulo_lemma (pow2 (n - s) - 1) (pow2 (n - s));
      M.modulo_addition_lemma (signed_min n - pow2 s) (signed_min n) 1;
      M.modulo_lemma (signed_min n - pow2 s) (signed_min n)
    )
    else (
      M.modulo_lemma (signed_max n) (pow2 n);
      M.modulo_lemma (signed_max n) (signed_min n)
    )
  )
  else (
    lemma_left_value s (bvlshr (signed_min n) s);
    U.logand_commutative 0 (signed_max n);
    U.logand_lemma_1 (signed_max n)
  )
#pop-options

let lemma_left_signed_bounds (#n:pos) (s x:bv n)
  : Lemma
    (to_int_signed (left_lower s) <= to_int_signed (bvshl x s) /\
     to_int_signed (bvshl x s) <= to_int_signed (left_upper s)) =
  lemma_left_value s x;
  M.pow2_double_mult (n - 1);
  if s < n then (
    M.pow2_plus (n - 1 - s) s;
    if not (msb (bvshl x s)) then (
      let k = x % pow2 (n - s) in
      let h = pow2 (n - 1 - s) in
      if k >= h then M.lemma_mult_le_left (pow2 s) h k
      else M.lemma_mult_le_left (pow2 s) k (h - 1)
    )
  )

let lemma_left_sle_condition (#n:pos) (s t:bv n)
  : Lemma (condition ShiftLeftValue I.Sle s t <==>
      I.holds I.Sle (left_lower s) t) =
  M.pow2_double_mult (n - 1);
  U.shift_right_value_lemma t s;
  if s < n then (
    M.pow2_le_compat (n - 1) s;
    if msb t then (
      M.division_definition_lemma_2 t (pow2 s) 1;
      S.lemma_right_positive t (bvlshr t s)
    )
    else S.lemma_right_bound t (bvlshr t s)
  )
  else (
    M.pow2_le_compat s n;
    M.small_div t (pow2 s);
    S.lemma_right_endpoints t
  )

let lemma_left_signed (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sgt \/ r = I.Sle \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition ShiftLeftValue r s t <==>
      (exists (x:bv n). I.holds r (apply ShiftLeftValue s x) t)) =
  lemma_left_signed_endpoints s;
  lemma_left_sle_condition s t;
  let x = if r = I.Slt || r = I.Sle then left_lower_witness s else left_upper_witness s in
  assert (condition ShiftLeftValue r s t ==>
    I.holds r (apply ShiftLeftValue s x) t);
  introduce forall x.
    to_int_signed (left_lower s) <= to_int_signed (bvshl x s) /\
    to_int_signed (bvshl x s) <= to_int_signed (left_upper s)
  with lemma_left_signed_bounds s x
#pop-options
