module Z3IndependentDefinitionContextEquivalence

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module Scope = Z3ExprScope
module Context = Z3IndependentDefinitionContext
module Eq = Z3IndependentDefinitionEquivalence

let rec lemma_matches (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (items:list (Context.item s inputs))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (fuel:nat) (a b:expr)
  : Lemma (requires Q.forall_model s bc other /\
      T.truths s bc eq other (Context.formulas s inputs items) /\
      Scope.scoped scope a /\ Scope.scoped scope b /\ matches s inputs items fuel a b)
    (ensures get_sort a == get_sort b /\
      T.evaluate_at s bc eq other scope rho a == T.evaluate_at s bc eq other scope rho b)
    (decreases items) =
  match items with
  | [] -> ()
  | item :: rest ->
    if Eq.equivalent fuel item.Context.definition a b then
      Eq.lemma_equivalent s bc eq other inputs item.Context.formula item.Context.domain
        item.Context.definition scope rho fuel a b
    else lemma_matches s bc eq other inputs rest scope rho fuel a b
