module Z3BvInvertibilityConcatProofs

open Z3BvTheory
open Z3BvInvertibilityConcat
module U = FStar.UInt
module I = Z3BvInvertibility
module C = Z3BvInvertibilityConditions
module O = Z3BvInvertibilityConcatOrder
module M = FStar.Math.Lemmas

#push-options "--fuel 3 --ifuel 1 --z3rlimit 20"
let lemma_endpoints (#n:pos) (x:bv n)
  : Lemma
    (0 <= x /\ x <= U.ones n /\
     to_int_signed (C.signed_min n) <= to_int_signed x /\
     to_int_signed x <= to_int_signed (C.signed_max n) /\
     (to_int_signed x == to_int_signed (C.signed_min n) <==> x == C.signed_min n) /\
     (to_int_signed x == to_int_signed (C.signed_max n) <==> x == C.signed_max n)) =
  O.lemma_range x;
  M.pow2_double_mult (n - 1);
  U.lognot_lemma_1 #n;
  O.lemma_signed_equal x (C.signed_min n);
  O.lemma_signed_equal x (C.signed_max n)

let lemma_sufficient (#n:pos) (#m:pos) (p:position) (r:I.relation)
  (s:bv m) (tx:bv n) (ts:bv m)
  : Lemma
    (condition p r s tx ts ==>
      I.holds r (apply p s (witness p r tx)) (apply p ts tx)) =
  lemma_endpoints tx;
  I.lemma_target I.Ne tx;
  let x = witness p r tx in
  match p with
  | High ->
    O.lemma_concat_order r x s tx ts;
    (match r with
    | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge | I.Slt | I.Sgt | I.Sle | I.Sge -> ())
  | Low ->
    O.lemma_concat_order r s x ts tx;
    O.lemma_signed_equal s ts;
    (match r with
    | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge | I.Slt | I.Sgt | I.Sle | I.Sge -> ())

let lemma_necessary (#n:pos) (#m:pos) (p:position) (r:I.relation)
  (s:bv m) (tx:bv n) (ts:bv m) (x:bv n)
  : Lemma
    (I.holds r (apply p s x) (apply p ts tx) ==>
      condition p r s tx ts) =
  lemma_endpoints x;
  lemma_endpoints tx;
  match p with
  | High ->
    O.lemma_concat_order r x s tx ts;
    (match r with
    | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge | I.Slt | I.Sgt | I.Sle | I.Sge -> ())
  | Low ->
    O.lemma_concat_order r s x ts tx;
    O.lemma_signed_equal s ts;
    (match r with
    | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge | I.Slt | I.Sgt | I.Sle | I.Sge -> ())

let lemma_invertibility (#n:pos) (#m:pos) (p:position) (r:I.relation)
  (s:bv m) (tx:bv n) (ts:bv m)
  : Lemma
    (condition p r s tx ts <==>
      (exists (x:bv n). I.holds r (apply p s x) (apply p ts tx))) =
  lemma_sufficient p r s tx ts;
  let x = witness p r tx in
  assert (condition p r s tx ts ==>
    I.holds r (apply p s x) (apply p ts tx));
  introduce forall x.
    I.holds r (apply p s x) (apply p ts tx) ==> condition p r s tx ts
  with lemma_necessary p r s tx ts x

let lemma_target_parts (#n:pos) (#m:pos) (p:position) (t:bv (n + m))
  : Lemma (apply p (fixed_part #n #m p t) (variable_part #n #m p t) == t) =
  match p with
  | High -> O.lemma_split #n #m t
  | Low -> O.lemma_split #m #n t

let lemma_invertibility_value (#n:pos) (#m:pos) (p:position) (r:I.relation)
  (s:bv m) (t:bv (n + m))
  : Lemma
    (condition_value #n #m p r s t <==>
      (exists (x:bv n). I.holds r (apply p s x) t)) =
  lemma_target_parts #n #m p t;
  lemma_invertibility p r s (variable_part #n #m p t) (fixed_part #n #m p t)
#pop-options
