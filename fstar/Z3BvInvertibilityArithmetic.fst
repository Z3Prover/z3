module Z3BvInvertibilityArithmetic

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module B = Z3BvInvertibilityBits
module M = FStar.Math.Lemmas

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let remainder_limit (#n:pos) (s:bv n) : bv n = bvnot (bvneg s)

let lemma_remainder_bound (#n:pos) (s x:bv n)
  : Lemma (apply RemainderValue s x <= remainder_limit s) =
  B.lemma_not_neg s;
  if s <> 0 then (
    M.lemma_div_mod x s;
    M.modulo_range_lemma x s
  )

let lemma_remainder_identity (#n:pos) (s:bv n)
  (x:bv n{x <= remainder_limit s})
  : Lemma (apply RemainderValue s x == x) =
  B.lemma_not_neg s;
  if s <> 0 then M.small_div x s

let remainder_witness (#n:pos) (r:I.unsigned_relation) (s t:bv n) : bv n =
  match r with
  | I.Eq -> t
  | I.Ne -> if t <> 0 then 0 else remainder_limit s
  | I.Ult | I.Ule -> 0
  | _ -> remainder_limit s

let lemma_remainder_sufficient (#n:pos) (r:I.unsigned_relation) (s t:bv n)
  : Lemma (condition RemainderValue r s t ==>
      I.holds r (apply RemainderValue s (remainder_witness r s t)) t) =
  B.lemma_not_neg s;
  U.lemma_uint_mod #n 0;
  U.lemma_one_mod_pow2 #n;
  lemma_remainder_identity s 0;
  lemma_remainder_identity s (remainder_limit s);
  match r with
  | I.Eq ->
    if condition RemainderValue r s t then lemma_remainder_identity s t
  | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge -> ()

let lemma_remainder_necessary (#n:pos) (r:I.unsigned_relation) (s t x:bv n)
  : Lemma (I.holds r (apply RemainderValue s x) t ==>
      condition RemainderValue r s t) =
  B.lemma_not_neg s;
  U.lemma_uint_mod #n 0;
  U.lemma_one_mod_pow2 #n;
  lemma_remainder_bound s x;
  match r with
  | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge -> ()

let lemma_remainder_unsigned (#n:pos) (r:I.unsigned_relation) (s t:bv n)
  : Lemma (condition RemainderValue r s t <==>
      (exists (x:bv n). I.holds r (apply RemainderValue s x) t)) =
  lemma_remainder_sufficient r s t;
  let x = remainder_witness r s t in
  assert (condition RemainderValue r s t ==>
    I.holds r (apply RemainderValue s x) t);
  introduce forall x. I.holds r (apply RemainderValue s x) t ==>
    condition RemainderValue r s t
  with lemma_remainder_necessary r s t x

let lemma_remainder_divisor_endpoints (#n:pos) (s:bv n)
  : Lemma
    (apply RemainderDivisor s 0 == s /\
     apply RemainderDivisor s 1 == 0) = ()

let lemma_remainder_divisor_bound (#n:pos) (s x:bv n)
  : Lemma (apply RemainderDivisor s x <= s) =
  if x <> 0 then (
    M.lemma_div_mod s x;
    M.lemma_mod_lt s x
  )

let lemma_remainder_divisor_neq (#n:pos) (s t:bv n)
  : Lemma (condition RemainderDivisor I.Ne s t <==>
      (exists (x:bv n). I.holds I.Ne (apply RemainderDivisor s x) t)) =
  U.lemma_uint_mod #n 0;
  lemma_remainder_divisor_endpoints s;
  let x:bv n = if s <> t then 0 else 1 in
  assert (condition RemainderDivisor I.Ne s t ==>
    I.holds I.Ne (apply RemainderDivisor s x) t);
  introduce forall y. I.holds I.Ne (apply RemainderDivisor s y) t ==>
    (s <> 0 \/ t <> 0)
  with lemma_remainder_divisor_bound s y

let lemma_remainder_divisor_ugt (#n:pos) (s t:bv n)
  : Lemma (condition RemainderDivisor I.Ugt s t <==>
      (exists (x:bv n). I.holds I.Ugt (apply RemainderDivisor s x) t)) =
  lemma_remainder_divisor_endpoints s;
  assert (condition RemainderDivisor I.Ugt s t ==>
    I.holds I.Ugt (apply RemainderDivisor s 0) t);
  introduce forall x. apply RemainderDivisor s x <= s
  with lemma_remainder_divisor_bound s x

let lemma_remainder_divisor_uge_condition (#n:pos) (s t:bv n)
  : Lemma (condition RemainderDivisor I.Uge s t <==> s >= t) =
  U.logand_le (bvsub (bvadd t t) s) s;
  assert (condition RemainderDivisor I.Uge s t ==
    (bvand (bvsub (bvadd t t) s) s >= t || t < s));
  if s < t then
    assert (bvand (bvsub (bvadd t t) s) s < t)
  else if t < s then
    assert (condition RemainderDivisor I.Uge s t)
  else (
    assert (s == t);
    U.lemma_sub_add_cancel t t;
    U.logand_self t;
    assert (bvand (bvsub (bvadd t t) s) s == t)
  )

let lemma_remainder_divisor_uge (#n:pos) (s t:bv n)
  : Lemma (condition RemainderDivisor I.Uge s t <==>
      (exists (x:bv n). I.holds I.Uge (apply RemainderDivisor s x) t)) =
  lemma_remainder_divisor_uge_condition s t;
  lemma_remainder_divisor_endpoints s;
  assert (condition RemainderDivisor I.Uge s t ==>
    I.holds I.Uge (apply RemainderDivisor s 0) t);
  introduce forall x. apply RemainderDivisor s x <= s
  with lemma_remainder_divisor_bound s x
let lemma_proper_remainder (#n:pos) (s x:bv n)
  : Lemma
    (let y = apply RemainderDivisor s x in y == s \/ 2 * y < s) =
  if x <> 0 then (
    M.lemma_div_mod s x;
    M.modulo_range_lemma s x;
    if s < x then M.small_div s x
    else (
      M.division_definition_lemma_2 s x 1;
      M.lemma_mult_le_left x 1 (s / x)
    )
  )

let half_remainder (#n:pos) (s:bv n) : bv n =
  if s = 0 then 0
  else (
    M.lemma_div_le (s - 1) (2 * (s - 1)) 2;
    (s - 1) / 2
  )

let half_remainder_witness (#n:pos) (s:bv n) : bv n =
  if s = 0 then 1
  else (
    M.division_propriety (s - 1) 2;
    s - half_remainder s
  )

let lemma_half_remainder_attained (#n:pos) (s:bv n)
  : Lemma
    (apply RemainderDivisor s (half_remainder_witness s) == half_remainder s) =
  if s <> 0 then (
    M.division_propriety (s - 1) 2;
    M.division_definition s (half_remainder_witness s) 1
  )

let signed_remainder_upper (#n:pos) (s:bv n) : bv n =
  if msb s then half_remainder s else s

let signed_remainder_witness (#n:pos) (s:bv n) : bv n =
  if msb s then half_remainder_witness s else 0

let lemma_remainder_signed_bounds (#n:pos) (s x:bv n)
  : Lemma
    (let y = apply RemainderDivisor s x in
     (if msb s then to_int_signed s else 0) <= to_int_signed y /\
     to_int_signed y <= to_int_signed (signed_remainder_upper s)) =
  lemma_remainder_divisor_bound s x;
  lemma_proper_remainder s x;
  M.pow2_double_mult (n - 1);
  let y = apply RemainderDivisor s x in
  if 2 * y < s then (
    M.division_definition_lemma_2 (s - 1) 2 y;
    if s <> 0 then M.division_propriety (s - 1) 2
  )

let lemma_remainder_signed_upper_attained (#n:pos) (s:bv n)
  : Lemma
    (apply RemainderDivisor s (signed_remainder_witness s) ==
      signed_remainder_upper s) =
  if msb s then lemma_half_remainder_attained s
  else lemma_remainder_divisor_endpoints s

let lemma_remainder_signed_lower (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sle}) (s t:bv n)
  : Lemma (condition RemainderDivisor r s t <==>
      (exists (x:bv n). I.holds r (apply RemainderDivisor s x) t)) =
  U.lemma_uint_mod #n 0;
  lemma_remainder_divisor_endpoints s;
  let x:bv n = if msb s then 0 else 1 in
  assert (condition RemainderDivisor r s t ==>
    I.holds r (apply RemainderDivisor s x) t);
  introduce forall x.
    (if msb s then to_int_signed s else 0) <=
      to_int_signed (apply RemainderDivisor s x)
  with lemma_remainder_signed_bounds s x

let lemma_remainder_signed_upper_condition (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition RemainderDivisor r s t <==>
      I.holds r (signed_remainder_upper s) t) =
  U.lemma_uint_mod #n 0;
  U.lemma_one_mod_pow2 #n;
  M.pow2_double_mult (n - 1);
  if msb s then (
    M.modulo_lemma (s - 1) (pow2 n);
    M.division_propriety (s - 1) 2;
    U.shift_right_value_lemma (bvsub s 1) 1;
    if not (msb t) then M.modulo_lemma (s - t) (pow2 n)
  )

let lemma_remainder_signed_upper (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition RemainderDivisor r s t <==>
      (exists (x:bv n). I.holds r (apply RemainderDivisor s x) t)) =
  lemma_remainder_signed_upper_condition r s t;
  lemma_remainder_signed_upper_attained s;
  let x = signed_remainder_witness s in
  assert (condition RemainderDivisor r s t ==>
    I.holds r (apply RemainderDivisor s x) t);
  introduce forall x.
    to_int_signed (apply RemainderDivisor s x) <=
      to_int_signed (signed_remainder_upper s)
  with lemma_remainder_signed_bounds s x
#pop-options
