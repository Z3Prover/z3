module Z3IndependentGroundDefinition

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Scope = Z3ExprScope
module Dependent = Z3SortedDependentSkolem
module R = Z3ClauseSyntax

let valid (s:S.checked_schema) (inputs:list expr) (formula:expr) (d:D.definition) : bool =
  let name = App d.D.symbol [] in
  d.D.symbol.domain = [] && d.D.variables = [] &&
  Dependent.function_safe s d.D.symbol &&
  Scope.scoped [] d.D.body && get_sort d.D.body = d.D.symbol.range &&
  D.fresh [d] d.D.body && D.fresh_args [d] inputs &&
  Scope.scoped [] formula &&
  (formula = R.mk_eq_expr name d.D.body || formula = R.mk_eq_expr d.D.body name)
let candidate (s:S.checked_schema) (inputs:list expr) (formula lhs rhs:expr)
  : result:option D.definition{
      match result with
      | Some d -> valid s inputs formula d
      | None -> True} =
  match lhs with
  | App f [] ->
    let d = { D.symbol = f; variables = []; body = rhs } in
    if valid s inputs formula d then Some d else None
  | _ -> None

let recognize (s:S.checked_schema) (inputs:list expr) (formula:expr)
  : result:option D.definition{
      match result with
      | Some d -> valid s inputs formula d
      | None -> True} =
  if None? (expression_budget 16384 formula) || None? (arguments_budget 2000000 inputs)
  then None
  else match formula with
  | App _ [lhs; rhs] ->
    (match candidate s inputs formula lhs rhs with
     | Some d -> Some d
     | None -> candidate s inputs formula rhs lhs)
  | _ -> None

type definition (s:S.checked_schema) (inputs:list expr) (formula:expr) =
  d:D.definition{valid s inputs formula d}

val override (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : V.interpretation base (S.signature s)

val lemma_override_application (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (f:func_decl) (args:V.arguments base (S.signature s) f.domain)
  : Lemma (requires f <> d.D.symbol)
    (ensures (override s bc eq other inputs formula d).V.application f args ==
             other.V.application f args)

val lemma_override_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma ((override s bc eq other inputs formula d).V.quantification ==
           other.V.quantification)

val lemma_fresh (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (scope:list sort) (rho:V.environment base (S.signature s) scope) (e:expr)
  : Lemma (requires Z3ExprScope.scoped scope e /\ D.fresh [d] e)
    (ensures T.evaluate_at s bc eq other scope rho e ==
             T.evaluate_at s bc eq (override s bc eq other inputs formula d) scope rho e)

val lemma_inputs (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (T.truths s bc eq (override s bc eq other inputs formula d) inputs ==
           T.truths s bc eq other inputs)

val lemma_definition (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (T.truth s bc eq (override s bc eq other inputs formula d) formula)
