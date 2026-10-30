module Z3BvInvertibilityComplete

open Z3BvTheory
open Z3BvInvertibilityConditions
module I = Z3BvInvertibility
module P = Z3BvInvertibilityProofs
module S = Z3BvInvertibilitySigned
module A = Z3BvInvertibilityArithmetic
module D = Z3BvInvertibilityDivision
module V = Z3BvInvertibilityDividend
module H = Z3BvInvertibilityShifts
module R = Z3BvInvertibilityRemainder
module L = Z3BvInvertibilityLogical
module C = Z3BvInvertibilityCarry
module M = Z3BvInvertibilityMultiply
module F = Z3BvInvertibilityFinal
module K = Z3BvInvertibilityConcat
module KP = Z3BvInvertibilityConcatProofs

let lemma_invertibility (#n:pos) (op:operator) (r:I.relation) (s t:bv n)
  : Lemma
    (condition op r s t <==>
      (exists (x:bv n). I.holds r (apply op s x) t)) =
  match op with
  | Negate | Complement | Add -> P.lemma_bijections op r s t
  | Conjoin ->
    (match r with
    | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge -> P.lemma_projections op r s t
    | I.Slt -> S.lemma_and_slt s t
    | I.Sgt -> S.lemma_and_sgt s t
    | I.Sle -> S.lemma_and_sle s t
    | I.Sge -> C.lemma_and_sge s t)
  | Disjoin ->
    (match r with
    | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge -> P.lemma_projections op r s t
    | I.Slt -> C.lemma_or_slt s t
    | I.Sgt -> S.lemma_or_sgt s t
    | I.Sle -> S.lemma_or_sle s t
    | I.Sge -> S.lemma_or_sge s t)
  | ShiftLeftValue ->
    (match r with
    | I.Eq -> L.lemma_logical_eq op s t
    | I.Ne -> P.lemma_logical_value_neq op s t
    | I.Ult | I.Ule -> P.lemma_zero_conditions op r s t
    | I.Ugt -> L.lemma_logical_ugt op s t
    | I.Uge -> L.lemma_left_uge s t
    | I.Slt | I.Sgt | I.Sle | I.Sge -> L.lemma_left_signed r s t)
  | ShiftLeftAmount ->
    (match r with
    | I.Eq | I.Ugt | I.Uge | I.Sgt | I.Sge -> P.lemma_enumerated_conditions op r s t
    | I.Ne -> P.lemma_shift_amount_neq op s t
    | I.Ult | I.Ule -> P.lemma_zero_conditions op r s t
    | I.Slt | I.Sle -> F.lemma_left_amount_signed r s t)
  | ShiftRightValue ->
    (match r with
    | I.Eq -> L.lemma_logical_eq op s t
    | I.Ne -> P.lemma_logical_value_neq op s t
    | I.Ult | I.Ule -> P.lemma_zero_conditions op r s t
    | I.Ugt -> L.lemma_logical_ugt op s t
    | I.Uge -> L.lemma_right_uge s t
    | I.Slt | I.Sle -> L.lemma_right_signed_lower r s t
    | I.Sgt | I.Sge -> L.lemma_right_signed_upper r s t)
  | ShiftRightAmount ->
    (match r with
    | I.Eq -> P.lemma_enumerated_conditions op r s t
    | I.Ne -> P.lemma_shift_amount_neq op s t
    | I.Ult | I.Ule -> P.lemma_zero_conditions op r s t
    | I.Ugt | I.Uge -> H.lemma_right_amount_unsigned r s t
    | I.Slt | I.Sle -> H.lemma_right_amount_signed_lower r s t
    | I.Sgt | I.Sge -> H.lemma_right_amount_signed_upper r s t)
  | ArithmeticRightValue ->
    (match r with
    | I.Eq -> F.lemma_ashr_eq s t
    | I.Ne | I.Ugt | I.Uge -> P.lemma_ashr_unsigned_endpoints r s t
    | I.Ult | I.Ule -> P.lemma_zero_conditions op r s t
    | I.Slt | I.Sgt | I.Sle | I.Sge -> H.lemma_ashr_value_signed r s t)
  | ArithmeticRightAmount ->
    (match r with
    | I.Eq -> P.lemma_enumerated_conditions op r s t
    | I.Ne -> H.lemma_ashr_amount_neq s t
    | I.Ult | I.Ugt | I.Ule | I.Uge -> H.lemma_ashr_amount_unsigned r s t
    | I.Slt | I.Sle -> H.lemma_ashr_amount_signed_lower r s t
    | I.Sgt | I.Sge -> H.lemma_ashr_amount_signed_upper r s t)
  | Multiply -> M.lemma_multiply r s t
  | Dividend ->
    (match r with
    | I.Eq -> V.lemma_dividend_eq s t
    | I.Ne -> P.lemma_dividend_neq s t
    | I.Ult -> P.lemma_dividend_ult s t
    | I.Ugt -> P.lemma_dividend_ugt s t
    | I.Ule -> V.lemma_dividend_ule s t
    | I.Uge -> V.lemma_dividend_uge s t
    | I.Slt -> V.lemma_dividend_slt s t
    | I.Sgt | I.Sge -> V.lemma_dividend_signed_upper r s t
    | I.Sle -> V.lemma_dividend_sle s t)
  | Divisor ->
    (match r with
    | I.Eq -> D.lemma_divisor_eq s t
    | I.Ne -> D.lemma_divisor_neq s t
    | I.Ult | I.Ule -> D.lemma_divisor_small r s t
    | I.Ugt | I.Uge -> P.lemma_divisor_unsigned_max r s t
    | I.Slt | I.Sle -> D.lemma_divisor_signed_lower r s t
    | I.Sgt | I.Sge -> D.lemma_divisor_signed_upper r s t)
  | RemainderValue ->
    (match r with
    | I.Eq | I.Ne | I.Ult | I.Ugt | I.Ule | I.Uge -> A.lemma_remainder_unsigned r s t
    | I.Slt | I.Sle -> R.lemma_signed_lower r s t
    | I.Sgt | I.Sge -> R.lemma_signed_upper r s t)
  | RemainderDivisor ->
    (match r with
    | I.Eq -> C.lemma_remainder_divisor_eq s t
    | I.Ne -> A.lemma_remainder_divisor_neq s t
    | I.Ult | I.Ule -> P.lemma_zero_conditions op r s t
    | I.Ugt -> A.lemma_remainder_divisor_ugt s t
    | I.Uge -> A.lemma_remainder_divisor_uge s t
    | I.Slt | I.Sle -> A.lemma_remainder_signed_lower r s t
    | I.Sgt | I.Sge -> A.lemma_remainder_signed_upper r s t)

let lemma_concat_invertibility (#n:pos) (#m:pos) (p:K.position) (r:I.relation)
  (s:bv m) (t:bv (n + m))
  : Lemma
    (K.condition_value #n #m p r s t <==>
      (exists (x:bv n). I.holds r (K.apply p s x) t)) =
  KP.lemma_invertibility_value #n #m p r s t
