module Z3BvInvertibilityDividend

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module P = Z3BvInvertibilityProofs
module B = Z3BvInvertibilityBits
module D = Z3BvInvertibilityDivision
module M = FStar.Math.Lemmas

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_dividend_eq_complete (#n:pos) (s t x:bv n)
  : Lemma (apply Dividend s x == t ==> condition Dividend I.Eq s t) =
  if apply Dividend s x = t then (
    if s > 0 then (
      M.division_propriety x s;
      assert (s * t < pow2 n);
      M.modulo_lemma (s * t) (pow2 n);
      M.cancel_mul_div t s
    )
  )

let lemma_dividend_eq (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Eq s t <==>
      (exists (x:bv n). I.holds I.Eq (apply Dividend s x) t)) =
  let x = bvmul s t in
  assert (condition Dividend I.Eq s t ==> I.holds I.Eq (apply Dividend s x) t);
  introduce forall x. I.holds I.Eq (apply Dividend s x) t ==>
    condition Dividend I.Eq s t
  with lemma_dividend_eq_complete s t x

#push-options "--fuel 1 --ifuel 1"
let lemma_dividend_ule_raw (#n:pos) (s t:bv n)
  : Lemma (bvor s t >= bvnot (bvneg s) <==> (s > 0 \/ t == U.ones n)) =
  B.lemma_not_neg s;
  U.logor_ge s t;
  U.logor_commutative 0 t;
  U.logor_lemma_1 t;
  assert (U.ones n == pow2 n - 1);
  if s > 0 then () else assert (s == 0)
#pop-options

let lemma_dividend_ule (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Ule s t <==>
      (exists (x:bv n). I.holds I.Ule (apply Dividend s x) t)) =
  U.lemma_uint_mod #n 0;
  lemma_dividend_ule_raw s t;
  P.lemma_division_endpoints s;
  assert (condition Dividend I.Ule s t <==> (s > 0 \/ t == U.ones n));
  assert (condition Dividend I.Ule s t ==> I.holds I.Ule (apply Dividend s 0) t);
  assert (forall (x:bv n). s = 0 ==> apply Dividend s x == U.ones n)

let lemma_dividend_uge_sufficient (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Uge s t ==>
      I.holds I.Uge (apply Dividend s (bvmul s t)) t) =
  if condition Dividend I.Uge s t then (
    if s > 0 && t > 0 then (
      let p = bvmul s t in
      let q = bvudiv p t in
      U.logand_le q s;
      assert (s <= q);
      M.division_propriety p t;
      M.lemma_mult_le_left t s q;
      assert (s * t < pow2 n);
      M.modulo_lemma (s * t) (pow2 n);
      M.cancel_mul_div t s
    )
  )

let lemma_dividend_uge_necessary (#n:pos) (s t x:bv n)
  : Lemma (I.holds I.Uge (apply Dividend s x) t ==>
      condition Dividend I.Uge s t) =
  if I.holds I.Uge (apply Dividend s x) t then (
    if s > 0 && t > 0 then (
      M.division_propriety x s;
      M.lemma_mult_le_left s t (x / s);
      M.modulo_lemma (s * t) (pow2 n);
      M.cancel_mul_div s t;
      U.logand_self s
    )
    else if t = 0 then (
      U.logand_commutative (U.ones n) s;
      U.logand_lemma_2 s
    )
    else (
      U.logand_le (bvudiv (bvmul s t) t) s
    )
  )

let lemma_dividend_uge (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Uge s t <==>
      (exists (x:bv n). I.holds I.Uge (apply Dividend s x) t)) =
  lemma_dividend_uge_sufficient s t;
  let x = bvmul s t in
  assert (condition Dividend I.Uge s t ==> I.holds I.Uge (apply Dividend s x) t);
  introduce forall x. I.holds I.Uge (apply Dividend s x) t ==>
    condition Dividend I.Uge s t
  with lemma_dividend_uge_necessary s t x

let dividend_signed_lower (#n:pos) (s:bv n) : bv n =
  if s = 0 then U.ones n else if s = 1 then signed_min n else 0

let dividend_lower_witness (#n:pos) (s:bv n) : bv n =
  if s = 1 then signed_min n else 0

let dividend_signed_upper (#n:pos) (s:bv n) : bv n =
  if s = 1 then signed_max n else bvudiv (U.ones n) s

let dividend_upper_witness (#n:pos) (s:bv n) : bv n =
  if s = 1 then signed_max n else U.ones n

let lemma_dividend_signed_bounds (#n:pos) (s x:bv n)
  : Lemma
    (to_int_signed (dividend_signed_lower s) <=
      to_int_signed (apply Dividend s x) /\
     to_int_signed (apply Dividend s x) <=
      to_int_signed (dividend_signed_upper s)) =
  P.lemma_dividend_max s x;
  M.pow2_double_mult (n - 1);
  if s >= 2 then (
    D.lemma_divisor_proper x s;
    D.lemma_divisor_proper (U.ones n) s
  )

let lemma_dividend_signed_endpoints (#n:pos) (s:bv n)
  : Lemma
    (apply Dividend s (dividend_lower_witness s) == dividend_signed_lower s /\
     apply Dividend s (dividend_upper_witness s) == dividend_signed_upper s) =
  P.lemma_division_endpoints s

let lemma_dividend_slt_condition (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Slt s t <==>
      I.holds I.Slt (dividend_signed_lower s) t) =
  U.lemma_uint_mod #n 0;
  lemma_dividend_signed_bounds s (signed_min n);
  if s >= 2 then D.lemma_divisor_proper (signed_min n) s

let lemma_dividend_slt (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Slt s t <==>
      (exists (x:bv n). I.holds I.Slt (apply Dividend s x) t)) =
  lemma_dividend_slt_condition s t;
  lemma_dividend_signed_endpoints s;
  let x = dividend_lower_witness s in
  assert (condition Dividend I.Slt s t ==> I.holds I.Slt (apply Dividend s x) t);
  introduce forall x.
    to_int_signed (dividend_signed_lower s) <= to_int_signed (apply Dividend s x)
  with lemma_dividend_signed_bounds s x

let lemma_dividend_sle_condition (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Sle s t <==>
      I.holds I.Sle (dividend_signed_lower s) t) =
  lemma_dividend_slt_condition s t;
  lemma_dividend_signed_endpoints s;
  lemma_dividend_signed_bounds s (bvmul s t);
  lemma_dividend_eq_complete s t (dividend_lower_witness s);
  M.pow2_double_mult (n - 1);
  assert (condition Dividend I.Sle s t ==
    (condition Dividend I.Eq s t || condition Dividend I.Slt s t));
  assert (to_int_signed (dividend_signed_lower s) == to_int_signed t ==>
    dividend_signed_lower s == t)

let lemma_dividend_sle (#n:pos) (s t:bv n)
  : Lemma (condition Dividend I.Sle s t <==>
      (exists (x:bv n). I.holds I.Sle (apply Dividend s x) t)) =
  lemma_dividend_sle_condition s t;
  lemma_dividend_signed_endpoints s;
  let x = dividend_lower_witness s in
  assert (condition Dividend I.Sle s t ==> I.holds I.Sle (apply Dividend s x) t);
  introduce forall x.
    to_int_signed (dividend_signed_lower s) <= to_int_signed (apply Dividend s x)
  with lemma_dividend_signed_bounds s x

let lemma_dividend_upper_condition (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition Dividend r s t <==>
      I.holds r (dividend_signed_upper s) t) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  assert (bvnot (bv_of_int #n 0) == U.ones n);
  lemma_dividend_signed_endpoints s;
  lemma_dividend_signed_bounds s (U.ones n);
  lemma_dividend_signed_bounds s (signed_max n);
  assert (dividend_upper_witness s == U.ones n \/
    dividend_upper_witness s == signed_max n);
  match r with
  | I.Sgt | I.Sge -> ()

let lemma_dividend_signed_upper (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition Dividend r s t <==>
      (exists (x:bv n). I.holds r (apply Dividend s x) t)) =
  lemma_dividend_signed_endpoints s;
  lemma_dividend_upper_condition r s t;
  let x = dividend_upper_witness s in
  assert (condition Dividend r s t <==>
    I.holds r (dividend_signed_upper s) t);
  assert (condition Dividend r s t ==> I.holds r (apply Dividend s x) t);
  introduce forall x.
    to_int_signed (apply Dividend s x) <= to_int_signed (dividend_signed_upper s)
  with lemma_dividend_signed_bounds s x
#pop-options
