module Z3BvInvertibilityProofs

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module M = FStar.Math.Lemmas

type bijective_operator = op:operator{
  op = Negate \/ op = Complement \/ op = Add}

#push-options "--fuel 5 --ifuel 2 --z3rlimit 20"
let lemma_bijections (#n:pos) (op:bijective_operator) (r:I.relation) (s t:bv n)
  : Lemma (condition op r s t <==> (exists (x:bv n). I.holds r (apply op s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  match op with
  | Negate -> I.lemma_bijection_invertibility I.Neg r s t
  | Complement -> I.lemma_bijection_invertibility I.Not r s t
  | Add -> I.lemma_bijection_invertibility I.Add r s t

type projection_operator = op:operator{op = Conjoin \/ op = Disjoin}

let lemma_projections (#n:pos) (op:projection_operator) (r:I.unsigned_relation)
  (s t:bv n)
  : Lemma (condition op r s t <==> (exists (x:bv n). I.holds r (apply op s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  match op with
  | Conjoin -> I.lemma_projection_invertibility I.And r s t
  | Disjoin -> I.lemma_projection_invertibility I.Or r s t
#pop-options

let rec lemma_width_fits (n:pos)
  : Lemma (n < pow2 n) (decreases n) =
  if n > 1 then (
    lemma_width_fits (n - 1);
    FStar.Math.Lemmas.pow2_double_mult (n - 1)
  )

type logical_value_operator = op:operator{
  op = ShiftLeftValue \/ op = ShiftRightValue}

let nonzero_shift_witness (#n:pos) (op:logical_value_operator)
  (s:bv n{s < n}) : bv n =
  match op with
  | ShiftLeftValue -> 1
  | ShiftRightValue -> U.pow2_n #n s

let lemma_nonzero_logical_shift (#n:pos) (op:logical_value_operator)
  (s:bv n{s < n})
  : Lemma (apply op s (nonzero_shift_witness op s) <> 0) =
  FStar.Math.Lemmas.pow2_lt_compat n s;
  match op with
  | ShiftLeftValue ->
    U.shift_left_value_lemma #n 1 s;
    U.lemma_uint_mod #n (pow2 s)
  | ShiftRightValue ->
    U.shift_right_value_lemma (U.pow2_n #n s) s

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_logical_value_neq (#n:pos) (op:logical_value_operator) (s t:bv n)
  : Lemma (condition op I.Ne s t <==>
      (exists (x:bv n). I.holds I.Ne (apply op s x) t)) =
  lemma_width_fits n;
  U.lemma_uint_mod #n n;
  U.lemma_uint_mod #n 0;
  (match op with
  | ShiftLeftValue -> U.shift_left_value_lemma #n 0 s
  | ShiftRightValue -> U.shift_right_value_lemma #n 0 s);
  assert (apply op s 0 == 0);
  if s < n then (
    lemma_nonzero_logical_shift op s;
    let x = if t <> 0 then 0 else nonzero_shift_witness op s in
    assert (I.holds I.Ne (apply op s x) t)
  )
  else (
    assert (t <> 0 ==> I.holds I.Ne (apply op s 0) t);
    introduce forall x. apply op s x == 0
    with (
      match op with
      | ShiftLeftValue -> U.shift_left_value_lemma x s
      | ShiftRightValue -> U.shift_right_value_lemma x s
    )
  )
#pop-options

let lemma_nat_prefix (p:nat -> Tot bool) (k:nat)
  : Lemma
    ((exists (i:nat). i <= k /\ p i) <==>
      (p k \/ (k > 0 /\ (exists (i:nat). i <= k - 1 /\ p i)))) = ()

let rec lemma_shift_disjunction (#n:pos) (op:operator) (r:I.relation)
  (s t:bv n) (k:nat)
  : Lemma
    (shift_disjunction op r s t k <==>
      (exists (i:nat). i <= k /\ I.holds r (apply op s (bv_of_int #n i)) t))
    (decreases k) =
  lemma_nat_prefix (fun i -> I.holds r (apply op s (bv_of_int #n i)) t) k;
  if k > 0 then lemma_shift_disjunction op r s t (k - 1)

type shift_operator = op:operator{
  op = ShiftLeftAmount \/ op = ShiftRightAmount \/ op = ArithmeticRightAmount}

let lemma_shift_saturation (#n:pos) (op:shift_operator) (s:bv n) (x:bv n{x >= n})
  : Lemma (apply op s x == apply op s (bv_of_int #n n)) =
  lemma_width_fits n;
  U.lemma_uint_mod #n n;
  match op with
  | ShiftLeftAmount ->
    U.shift_left_value_lemma s x;
    U.shift_left_value_lemma s n
  | ShiftRightAmount ->
    U.shift_right_value_lemma s x;
    U.shift_right_value_lemma s n
  | ArithmeticRightAmount ->
    I.lemma_ashr_large s x;
    I.lemma_ashr_large s n

let lemma_shift_witness_bound (#n:pos) (op:shift_operator) (r:I.relation)
  (s t x:bv n)
  : Lemma
    (I.holds r (apply op s x) t ==>
      (exists (i:nat). i <= n /\ I.holds r (apply op s (bv_of_int #n i)) t)) =
  if x < n then (
    U.lemma_uint_mod x;
    assert (x <= n /\ (I.holds r (apply op s x) t ==>
      I.holds r (apply op s (bv_of_int #n x)) t))
  )
  else (
    lemma_shift_saturation op s x;
    assert (I.holds r (apply op s x) t ==>
      I.holds r (apply op s (bv_of_int #n n)) t)
  )

let lemma_variable_shift (#n:pos) (op:shift_operator) (r:I.relation) (s t:bv n)
  : Lemma
    (shift_disjunction op r s t n <==>
      (exists (x:bv n). I.holds r (apply op s x) t)) =
  lemma_shift_disjunction op r s t n;
  introduce forall x. I.holds r (apply op s x) t ==>
    (exists (i:nat). i <= n /\ I.holds r (apply op s (bv_of_int #n i)) t)
  with lemma_shift_witness_bound op r s t x

type enumerated_relation (op:shift_operator) = r:I.relation{
  r = I.Eq \/ (op = ShiftLeftAmount /\
    (r = I.Ugt \/ r = I.Uge \/ r = I.Sgt \/ r = I.Sge))}

let lemma_enumerated_conditions (#n:pos) (op:shift_operator)
  (r:enumerated_relation op) (s t:bv n)
  : Lemma (condition op r s t <==> (exists (x:bv n). I.holds r (apply op s x) t)) =
  lemma_variable_shift op r s t

type zero_operator = op:operator{
  op = ShiftLeftValue \/ op = ShiftRightValue \/ op = ShiftLeftAmount \/
  op = ShiftRightAmount \/ op = ArithmeticRightValue \/ op = Multiply \/
  op = RemainderValue \/ op = RemainderDivisor}

let zero_witness (#n:pos) (op:zero_operator) : bv n =
  match op with
  | ShiftLeftAmount | ShiftRightAmount ->
    lemma_width_fits n;
    n
  | RemainderDivisor -> 1
  | _ -> 0

let lemma_zero_attained (#n:pos) (op:zero_operator) (s:bv n)
  : Lemma (apply op s (zero_witness #n op) == 0) =
  match op with
  | ShiftLeftValue -> U.shift_left_value_lemma #n 0 s
  | ShiftRightValue | ArithmeticRightValue -> U.shift_right_value_lemma #n 0 s
  | ShiftLeftAmount -> U.shift_left_value_lemma s n
  | ShiftRightAmount -> U.shift_right_value_lemma s n
  | Multiply | RemainderValue | RemainderDivisor -> ()

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_zero_conditions (#n:pos) (op:zero_operator)
  (r:I.relation{r = I.Ult \/ r = I.Ule}) (s t:bv n)
  : Lemma (condition op r s t <==> (exists (x:bv n). I.holds r (apply op s x) t)) =
  U.lemma_uint_mod #n 0;
  lemma_zero_attained op s;
  I.lemma_target r t;
  let x = zero_witness #n op in
  assert (I.unconstrained_condition r t ==> I.holds r (apply op s x) t);
  assert (condition op r s t <==> I.unconstrained_condition r t);
  introduce forall x. I.holds r (apply op s x) t ==> I.unconstrained_condition r t
  with I.lemma_target_necessary r (apply op s x) t
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_ashr_ones (#n:pos) (s:bv n)
  : Lemma (apply ArithmeticRightValue s (U.ones n) == U.ones n) =
  U.lemma_lognot_value_mod (U.ones n);
  FStar.Math.Lemmas.pow2_double_mult (n - 1);
  assert (bvnot (U.ones n) == 0);
  assert (msb (U.ones n));
  U.shift_right_value_lemma #n 0 s;
  M.small_div 0 (pow2 s);
  assert (bvlshr #n 0 s == 0);
  U.lognot_lemma_1 #n;
  assert (bvashr (U.ones n) s == U.ones n)

let lemma_ashr_unsigned_endpoints (#n:pos)
  (r:I.relation{r = I.Ne \/ r = I.Ugt \/ r = I.Uge}) (s t:bv n)
  : Lemma (condition ArithmeticRightValue r s t <==>
      (exists (x:bv n). I.holds r (apply ArithmeticRightValue s x) t)) =
  lemma_zero_attained ArithmeticRightValue s;
  lemma_ashr_ones s;
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  let x = if r = I.Ne && t <> 0 then 0 else U.ones n in
  assert (condition ArithmeticRightValue r s t ==>
    I.holds r (apply ArithmeticRightValue s x) t);
  introduce forall x. I.holds r (apply ArithmeticRightValue s x) t ==>
    I.unconstrained_condition r t
  with I.lemma_target_necessary r (apply ArithmeticRightValue s x) t

let lemma_multiply_neq (#n:pos) (s t:bv n)
  : Lemma (condition Multiply I.Ne s t <==>
      (exists (x:bv n). I.holds I.Ne (apply Multiply s x) t)) =
  U.lemma_uint_mod s;
  U.lemma_uint_mod #n 0;
  let x:bv n = if t = 0 then 1 else 0 in
  assert (condition Multiply I.Ne s t ==> I.holds I.Ne (apply Multiply s x) t);
  assert (forall (y:bv n). s = 0 ==> apply Multiply s y == 0)

let lemma_shift_amount_neq (#n:pos)
  (op:operator{op = ShiftLeftAmount \/ op = ShiftRightAmount}) (s t:bv n)
  : Lemma (condition op I.Ne s t <==>
      (exists (x:bv n). I.holds I.Ne (apply op s x) t)) =
  lemma_width_fits n;
  U.lemma_uint_mod #n n;
  U.lemma_uint_mod #n 0;
  lemma_zero_attained op s;
  (match op with
  | ShiftLeftAmount -> U.shift_left_value_lemma s 0
  | ShiftRightAmount -> U.shift_right_value_lemma s 0);
  let x:bv n = if s <> t then 0 else n in
  assert (condition op I.Ne s t ==> I.holds I.Ne (apply op s x) t);
  introduce forall y. I.holds I.Ne (apply op s y) t ==> (s <> 0 \/ t <> 0)
  with (
    match op with
    | ShiftLeftAmount -> U.shift_left_value_lemma s y
    | ShiftRightAmount -> U.shift_right_value_lemma s y
  )
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_division_endpoints (#n:pos) (s:bv n)
  : Lemma
    (apply Dividend s 0 == (if s = 0 then U.ones n else 0) /\
     apply Dividend s s == (if s = 0 then U.ones n else 1) /\
     apply Divisor s 0 == U.ones n /\
     apply Divisor s 1 == s) =
  if s <> 0 then (
    M.small_div 0 s;
    M.cancel_mul_div 1 s
  )

let lemma_dividend_ult (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Ult s t <==>
      (exists (x:bv n). I.holds I.Ult (apply Dividend s x) t)) =
  U.lemma_uint_mod #n 0;
  lemma_division_endpoints s;
  assert (condition Dividend I.Ult s t ==> I.holds I.Ult (apply Dividend s 0) t);
  assert (forall (x:bv n). s = 0 ==> apply Dividend s x == U.ones n)

let lemma_dividend_neq (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Ne s t <==>
      (exists (x:bv n). I.holds I.Ne (apply Dividend s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  lemma_division_endpoints s;
  let x = if s = 0 || t <> 0 then 0 else s in
  assert (condition Dividend I.Ne s t ==> I.holds I.Ne (apply Dividend s x) t);
  assert (forall (y:bv n). s = 0 ==> apply Dividend s y == U.ones n)

let lemma_dividend_max (#n:pos) (s x:bv n)
  : Lemma (apply Dividend s x <= apply Dividend s (U.ones n)) =
  if s <> 0 then M.lemma_div_le x (U.ones n) s

let lemma_dividend_ugt (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Ugt s t <==>
      (exists (x:bv n). I.holds I.Ugt (apply Dividend s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  assert (condition Dividend I.Ugt s t ==>
    I.holds I.Ugt (apply Dividend s (U.ones n)) t);
  introduce forall x. apply Dividend s x <= apply Dividend s (U.ones n)
  with lemma_dividend_max s x

let lemma_divisor_unsigned_max (#n:pos)
  (r:I.relation{r = I.Ugt \/ r = I.Uge}) (s t:bv n)
  : Lemma (condition Divisor r s t <==>
      (exists (x:bv n). I.holds r (apply Divisor s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  lemma_division_endpoints s;
  assert (condition Divisor r s t ==> I.holds r (apply Divisor s 0) t);
  introduce forall x. I.holds r (apply Divisor s x) t ==> I.unconstrained_condition r t
  with I.lemma_target_necessary r (apply Divisor s x) t
#pop-options
