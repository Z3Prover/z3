module Z3SortedCommutativity

open Z3AstTheory
module C = Z3CommutativitySyntax
module D = Z3ExprScope
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module I = Z3SortedInteger
module A = Z3SortedArithmetic

let lemma_step (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
               (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
               (scope:list sort) (rho:V.environment base (S.signature s) scope)
               (a b:expr)
  : Lemma (requires D.scoped scope a /\ D.scoped scope b /\ C.commutativity_step a b)
          (ensures T.evaluate_at s bc model other scope rho a ==
                   T.evaluate_at s bc model other scope rho b) =
  match a, b with
  | App f [x; y], App _ [_; _] ->
    if C.arithmetic_decl f then (
      A.lemma_application s bc model other scope rho f [x; y];
      A.lemma_application s bc model other scope rho f [y; x]
    ) else (
      T.lemma_evaluate_core_at s bc model other scope rho f [x; y];
      T.lemma_evaluate_core_at s bc model other scope rho f [y; x];
      match T.classify f with
      | T.Equality _ ->
        T.lemma_equal_tree model.T.reflection
          (T.evaluate_at s bc model other scope rho x)
          (T.evaluate_at s bc model other scope rho y);
        T.lemma_equal_tree model.T.reflection
          (T.evaluate_at s bc model other scope rho y)
          (T.evaluate_at s bc model other scope rho x)
      | _ -> ()
    )
  | _, _ -> ()
