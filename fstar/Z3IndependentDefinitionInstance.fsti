module Z3IndependentDefinitionInstance

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module Scope = Z3ExprScope
module Sub = Z3Substitution
module Model = Z3IndependentDefinitionModel

val lemma_instance (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:Model.definition s inputs formula)
  (scope:list sort) (rho:V.environment base (S.signature s) scope) (arg result:expr)
  : Lemma (requires d.Z3DefinitionSyntax.symbol.domain == [t] /\
      Q.forall_model s bc other /\ T.truth s bc eq other formula /\
      Scope.scoped scope arg /\ get_sort arg == t /\
      Sub.substitute [arg] d.Z3DefinitionSyntax.body == Some result)
    (ensures Scope.scoped scope result /\ get_sort result == bool_sort /\
      T.evaluate_at s bc eq other scope rho (App d.Z3DefinitionSyntax.symbol [arg]) ==
      T.evaluate_at s bc eq other scope rho result)
