module Z3BvInvertibilityRemainder

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module A = Z3BvInvertibilityArithmetic
module B = Z3BvInvertibilityBits
module M = FStar.Math.Lemmas

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let signed_lower (#n:pos) (s:bv n) : bv n =
  if s = 0 || s > signed_min n then signed_min n else 0

let signed_upper (#n:pos) (s:bv n) : bv n =
  if s > 0 && s < signed_min n then s - 1 else signed_max n

let lemma_signed_endpoints (#n:pos) (s:bv n)
  : Lemma
    (apply RemainderValue s (signed_lower s) == signed_lower s /\
     apply RemainderValue s (signed_upper s) == signed_upper s) =
  B.lemma_not_neg s;
  M.pow2_double_mult (n - 1);
  A.lemma_remainder_identity s (signed_lower s);
  A.lemma_remainder_identity s (signed_upper s)

let lemma_signed_bounds (#n:pos) (s x:bv n)
  : Lemma
    (to_int_signed (signed_lower s) <= to_int_signed (apply RemainderValue s x) /\
     to_int_signed (apply RemainderValue s x) <= to_int_signed (signed_upper s)) =
  A.lemma_remainder_bound s x;
  B.lemma_not_neg s;
  M.pow2_double_mult (n - 1)

#push-options "--fuel 1 --ifuel 1"
let lemma_neg_value (#n:pos) (a:bv n)
  : Lemma (bvneg a == (if a = 0 then 0 else pow2 n - a)) =
  B.lemma_not_neg a;
  U.lemma_lognot_value_mod (bvneg a)

let lemma_lower_raw (#n:pos) (s t:bv n)
  : Lemma
    ((I.holds I.Slt (bvnot t) (bvor (bvneg s) (bvneg t)) <==>
       to_int_signed (signed_lower s) < to_int_signed t) /\
     (I.holds I.Slt (U.ones n) (bvand (bvneg s) t) <==>
       to_int_signed (signed_lower s) <= to_int_signed t)) =
  lemma_neg_value s;
  lemma_neg_value t;
  U.lemma_lognot_value_mod t;
  B.lemma_bitwise_sign (bvneg s) (bvneg t);
  B.lemma_bitwise_sign (bvneg s) t;
  U.logor_ge (bvneg s) (bvneg t);
  M.pow2_double_mult (n - 1);
  assert (U.ones n == pow2 n - 1);
  if t > 0 then () else (
    assert (t == 0);
    U.logor_lemma_1 (bvneg s)
  )
#pop-options

let lemma_signed_lower (#n:pos)
  (r:I.relation{r = I.Slt \/ r = I.Sle}) (s t:bv n)
  : Lemma (condition RemainderValue r s t <==>
      (exists (x:bv n). I.holds r (apply RemainderValue s x) t)) =
  U.lemma_uint_mod #n 0;
  U.lognot_lemma_1 #n;
  lemma_lower_raw s t;
  lemma_signed_endpoints s;
  let x = signed_lower s in
  assert (condition RemainderValue r s t <==> I.holds r x t);
  assert (condition RemainderValue r s t ==>
    I.holds r (apply RemainderValue s x) t);
  introduce forall x.
    to_int_signed (signed_lower s) <= to_int_signed (apply RemainderValue s x)
  with lemma_signed_bounds s x

let lemma_upper_condition (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition RemainderValue r s t <==> I.holds r (signed_upper s) t) =
  U.lemma_uint_mod #n 0;
  U.lemma_one_mod_pow2 #n;
  B.lemma_not_neg s;
  M.pow2_double_mult (n - 1);
  match r with
  | I.Sgt | I.Sge -> ()

let lemma_signed_upper (#n:pos)
  (r:I.relation{r = I.Sgt \/ r = I.Sge}) (s t:bv n)
  : Lemma (condition RemainderValue r s t <==>
      (exists (x:bv n). I.holds r (apply RemainderValue s x) t)) =
  lemma_upper_condition r s t;
  lemma_signed_endpoints s;
  let x = signed_upper s in
  assert (condition RemainderValue r s t ==>
    I.holds r (apply RemainderValue s x) t);
  introduce forall x.
    to_int_signed (apply RemainderValue s x) <= to_int_signed (signed_upper s)
  with lemma_signed_bounds s x
#pop-options
