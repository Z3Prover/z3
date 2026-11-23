module Z3IndependentDefinitionPair

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module Scope = Z3ExprScope
module Dependent = Z3SortedDependentSkolem
module R = Z3ClauseSyntax
module A = Z3ArraySyntax

val pair (t:sort) (d:D.definition)
  : result:expr{result ==
      (let name = App d.D.symbol [Var 0 t] in
       let left = [R.mk_not_expr name; d.D.body] in
       let right = [name; R.mk_not_expr d.D.body] in
       let positive = Quantifier Forall_k [t] bool_sort (App (R.or_decl left) left) in
       let negative = Quantifier Forall_k [t] bool_sort (App (R.or_decl right) right) in
       let args = [positive; negative] in
       App (R.and_decl args) args)}
val scalar_pair (condition name then_value else_value:expr)
  : result:expr{result ==
      (let positive = App (R.or_decl [R.mk_not_expr condition; R.mk_eq_expr name then_value])
                          [R.mk_not_expr condition; R.mk_eq_expr name then_value] in
       let negative = App (R.or_decl [condition; R.mk_eq_expr name else_value])
                          [condition; R.mk_eq_expr name else_value] in
       App (R.and_decl [positive; negative]) [positive; negative])}
val scalar_valid (s:S.checked_schema) (inputs:list expr) (formula:expr) (d:D.definition)
  : result:bool{result ==
      (d.D.symbol.domain = [] && d.D.variables = [] &&
       Dependent.function_safe s d.D.symbol &&
       get_sort d.D.body = d.D.symbol.range &&
       D.fresh [d] d.D.body && D.fresh_args [d] inputs &&
       Scope.scoped [] (App d.D.symbol []) &&
       Scope.scoped [] d.D.body && Scope.scoped [] formula &&
       (match A.ite_parts d.D.body with
        | Some (condition, then_value, else_value) ->
          formula = scalar_pair condition (App d.D.symbol []) then_value else_value
        | None -> false))}
val valid (s:S.checked_schema) (inputs:list expr) (formula:expr) (d:D.definition)
  : result:bool{result == (match d.D.symbol.domain with
      | [t] ->
        Dependent.function_safe s d.D.symbol &&
        d.D.symbol.range = bool_sort &&
        D.make_definition [t] (App d.D.symbol [Var 0 t]) d.D.body = Some d &&
        D.fresh [d] d.D.body && D.fresh_args [d] inputs &&
        Scope.scoped [] formula && formula = pair t d
      | [] -> scalar_valid s inputs formula d
      | _ -> false)}
val recognize (s:S.checked_schema) (inputs:list expr) (formula:expr)
  : result:option D.definition{
      match result with
      | Some d -> valid s inputs formula d
      | None -> True}

val lemma_pair_truth (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:D.definition) (t:sort)
  : Lemma (requires valid s inputs formula d /\ d.D.symbol.domain == [t] /\
      Q.forall_model s bc other /\
      (forall (rho:V.environment base (S.signature s) [t]).
        T.truth_at s bc eq other [t] rho (App d.D.symbol [Var 0 t]) <==>
        T.truth_at s bc eq other [t] rho d.D.body))
    (ensures T.truth s bc eq other formula)

val lemma_pair_pointwise (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:D.definition) (t:sort)
  (rho:V.environment base (S.signature s) [t])
  : Lemma (requires valid s inputs formula d /\ d.D.symbol.domain == [t] /\
      Q.forall_model s bc other /\ T.truth s bc eq other formula)
    (ensures T.truth_at s bc eq other [t] rho (App d.D.symbol [Var 0 t]) <==>
             T.truth_at s bc eq other [t] rho d.D.body)

val lemma_scalar_pair_truth (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:D.definition)
  : Lemma (requires scalar_valid s inputs formula d /\
      T.evaluate s bc eq other (App d.D.symbol []) ==
      T.evaluate s bc eq other d.D.body)
    (ensures T.truth s bc eq other formula)
