module Z3IndependentDefinitionInstance

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module Scope = Z3ExprScope
module Sub = Z3Substitution
module Binding = Z3SortedBinding
module Model = Z3IndependentDefinitionModel
module Pair = Z3IndependentDefinitionPair
module L = FStar.List.Tot

let lemma_instance (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:Model.definition s inputs formula t)
  (scope:list sort) (rho:V.environment base (S.signature s) scope) (arg result:expr)
  : Lemma (requires Q.forall_model s bc other /\ T.truth s bc eq other formula /\
      Scope.scoped scope arg /\ get_sort arg == t /\
      Sub.substitute [arg] d.D.body == Some result)
    (ensures Scope.scoped scope result /\ get_sort result == bool_sort /\
      T.evaluate_at s bc eq other scope rho (App d.D.symbol [arg]) ==
      T.evaluate_at s bc eq other scope rho result) =
  let sigma = S.signature s in
  let i = T.interpretation s bc eq other in
  let value = T.evaluate_at s bc eq other scope rho arg in
  let env = V.extend sigma [] [t] [value] (T.empty_environment sigma) in
  let theta = Sub.arguments [arg] in
  let at (n:nat{n < L.length [t]})
    : Lemma (match theta n (L.index [t] n) with
      | Some e -> Scope.scoped scope e /\ get_sort e == L.index [t] n /\
                  env n == V.evaluate sigma i scope rho e
      | None -> True) =
    assert_norm (L.length [t] == 1);
    assert (n == 0) in
  FStar.Classical.forall_intro at;
  Binding.lemma_substitution_scopes_of_environments sigma i theta [t] scope env rho;
  Binding.lemma_apply_scope theta [t] scope d.D.body result;
  Binding.lemma_apply sigma i theta [t] scope env rho d.D.body result;
  Pair.lemma_pair_pointwise s bc eq other inputs formula d t env;
  let name = App d.D.symbol [Var 0 t] in
  T.lemma_boolean s bc (T.evaluate_at s bc eq other [t] env name);
  T.lemma_boolean s bc (T.evaluate_at s bc eq other [t] env d.D.body)
