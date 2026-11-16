module Z3IndependentIteAdd

open Z3AstTheory
module A = Z3LinearArithmeticAst
module AR = Z3SortedArithmetic
module D = Z3ExprScope
module I = Z3SortedInteger
module NR = Z3NnfReplay
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let check (lhs rhs:expr) : bool =
  match lhs, rhs with
  | App outer [c; App inner [d; App add1 [x; k1]; App add2 [y; k2]]; k3],
    App add3 [App outer' [c'; App inner' [d'; x'; y']; zero]; k] ->
    T.classify outer = T.Choice A.int_s &&
    T.classify inner = T.Choice A.int_s &&
    T.classify outer' = T.Choice A.int_s &&
    T.classify inner' = T.Choice A.int_s &&
    I.classify add1 = I.Calculate A.Add &&
    I.classify add2 = I.Calculate A.Add &&
    I.classify add3 = I.Calculate A.Add &&
    AR.int_numeral 0 zero &&
    c = c' && d = d' && x = x' && y = y' &&
    k = k1 && k = k2 && k = k3
  | _, _ -> false

let lemma_add (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (f:func_decl) (x y:expr)
  : Lemma (requires D.scoped scope (App f [x; y]) /\ I.classify f == I.Calculate A.Add)
          (ensures AR.integer s bc model other scope rho (App f [x; y]) ==
                   AR.integer s bc model other scope rho x + AR.integer s bc model other scope rho y) =
  I.lemma_argument_sorts [x; y] f.domain;
  AR.lemma_application s bc model other scope rho f [x; y]

let lemma_check (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (lhs rhs:expr)
  : Lemma (requires D.scoped scope lhs /\ D.scoped scope rhs /\ check lhs rhs)
          (ensures T.evaluate_at s bc model other scope rho lhs ==
                   T.evaluate_at s bc model other scope rho rhs) =
  match lhs, rhs with
  | App outer [c; App inner [d; App add1 [x; k1]; App add2 [y; k2]]; k3],
    App add3 [App outer' [c'; App inner' [d'; x'; y']; zero]; k] ->
    NR.lemma_value_ite s bc model other scope rho outer c
      (App inner [d; App add1 [x; k1]; App add2 [y; k2]]) k3;
    NR.lemma_value_ite s bc model other scope rho inner d
      (App add1 [x; k1]) (App add2 [y; k2]);
    NR.lemma_value_ite s bc model other scope rho outer' c'
      (App inner' [d'; x'; y']) zero;
    NR.lemma_value_ite s bc model other scope rho inner' d' x' y';
    lemma_add s bc model other scope rho add1 x k1;
    lemma_add s bc model other scope rho add2 y k2;
    lemma_add s bc model other scope rho add3 (App outer' [c'; App inner' [d'; x'; y']; zero]) k;
    AR.lemma_int_numeral s bc model other scope rho 0 zero;
    AR.lemma_integer_equality s bc model other scope rho lhs rhs
  | _, _ -> ()
