module Z3BvInvertibilitySigned

open Z3BvTheory
open Z3BvInvertibilityConditions
module U = FStar.UInt
module I = Z3BvInvertibility
module B = Z3BvInvertibilityBits
module M = FStar.Math.Lemmas

#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_and_sgt (#n:pos) (s t:bv n)
  : Lemma (condition Conjoin I.Sgt s t <==>
      (exists (x:bv n). I.holds I.Sgt (apply Conjoin s x) t)) =
  U.logand_commutative s (signed_max n);
  assert (condition Conjoin I.Sgt s t ==>
    I.holds I.Sgt (apply Conjoin s (signed_max n)) t);
  introduce forall x.
    to_int_signed (apply Conjoin s x) <= to_int_signed (bvand (signed_max n) s)
  with B.lemma_and_signed_bounds s x

let lemma_and_sle (#n:pos) (s t:bv n)
  : Lemma (condition Conjoin I.Sle s t <==>
      (exists (x:bv n). I.holds I.Sle (apply Conjoin s x) t)) =
  B.lemma_sign_mask s;
  B.lemma_sign_mask t;
  U.logand_commutative (signed_min n) s;
  M.pow2_double_mult (n - 1);
  assert (condition Conjoin I.Sle s t <==>
    I.holds I.Sle (apply Conjoin s (signed_min n)) t);
  introduce forall x.
    to_int_signed (bvand (signed_min n) s) <= to_int_signed (apply Conjoin s x)
  with B.lemma_and_signed_bounds s x

let lemma_and_slt (#n:pos) (s t:bv n)
  : Lemma (condition Conjoin I.Slt s t <==>
      (exists (x:bv n). I.holds I.Slt (apply Conjoin s x) t)) =
  assert (condition Conjoin I.Slt s t ==>
    I.holds I.Slt (apply Conjoin s (bvnot (bvneg t))) t);
  introduce forall x. I.holds I.Slt (apply Conjoin s x) t ==>
    condition Conjoin I.Slt s t
  with (
    B.lemma_and_signed_bounds s x;
    B.lemma_and_predecessor s t
  )

let lemma_or_sgt (#n:pos) (s t:bv n)
  : Lemma (condition Disjoin I.Sgt s t <==>
      (exists (x:bv n). I.holds I.Sgt (apply Disjoin s x) t)) =
  U.logor_commutative s (signed_max n);
  assert (condition Disjoin I.Sgt s t ==>
    I.holds I.Sgt (apply Disjoin s (signed_max n)) t);
  introduce forall x.
    to_int_signed (apply Disjoin s x) <= to_int_signed (bvor (signed_max n) s)
  with B.lemma_or_signed_bounds s x

let lemma_or_sle (#n:pos) (s t:bv n)
  : Lemma (condition Disjoin I.Sle s t <==>
      (exists (x:bv n). I.holds I.Sle (apply Disjoin s x) t)) =
  U.logor_commutative s (signed_min n);
  assert (condition Disjoin I.Sle s t ==>
    I.holds I.Sle (apply Disjoin s (signed_min n)) t);
  introduce forall x.
    to_int_signed (bvor (signed_min n) s) <= to_int_signed (apply Disjoin s x)
  with B.lemma_or_signed_bounds s x

let lemma_or_sge (#n:pos) (s t:bv n)
  : Lemma (condition Disjoin I.Sge s t <==>
      (exists (x:bv n). I.holds I.Sge (apply Disjoin s x) t)) =
  B.lemma_bitwise_sign s t;
  U.logand_le s t;
  B.lemma_or_signed_max s;
  M.pow2_double_mult (n - 1);
  assert (condition Disjoin I.Sge s t <==>
    I.holds I.Sge (apply Disjoin s (signed_max n)) t);
  introduce forall x.
    to_int_signed (apply Disjoin s x) <= to_int_signed (bvor (signed_max n) s)
  with B.lemma_or_signed_bounds s x
#pop-options
