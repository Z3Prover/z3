module Z3IndependentDefinitionInstanceTests

open Z3AstTheory
module X = Z3IndependentDefinitionModelTests
module D = Z3DefinitionSyntax
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module Root = Z3SortedRootDocument
module Pair = Z3IndependentDefinitionPair
module Model = Z3IndependentDefinitionModel
module Instance = Z3IndependentDefinitionInstance
module Sub = Z3Substitution
module Scope = Z3ExprScope
module Dependent = Z3SortedDependentSkolem

let body = Quantifier Exists_k [X.domain] bool_sort
  (R.mk_eq_expr (Var 1 X.domain) (Var 0 X.domain))
let raw : D.definition = { D.symbol = X.symbol; variables = [0]; body = body }
let formula =
  let name = App X.symbol [Var 0 X.domain] in
  let left = [R.mk_not_expr name; body] in
  let right = [name; R.mk_not_expr body] in
  let args = [
    Quantifier Forall_k [X.domain] bool_sort (App (R.or_decl left) left);
    Quantifier Forall_k [X.domain] bool_sort (App (R.or_decl right) right)
  ] in
  App (R.and_decl args) args
let definition : Model.definition X.schema X.inputs formula =
  assert_norm (Dependent.function_safe X.schema X.symbol);
  assert_norm (D.make_definition [X.domain] (App X.symbol [Var 0 X.domain]) body == Some raw);
  assert_norm (D.fresh [raw] body /\ D.fresh_args [raw] X.inputs);
  assert_norm (Scope.scoped [] formula);
  let paired = Pair.pair X.domain raw in
  assert (paired == formula);
  let accepted = Pair.valid X.schema X.inputs formula raw in
  assert (accepted);
  raw

let argument = Var 1 X.domain
let result = Quantifier Exists_k [X.domain] bool_sort
  (R.mk_eq_expr (Var 2 X.domain) (Var 0 X.domain))
let captured = Quantifier Exists_k [X.domain] bool_sort
  (R.mk_eq_expr (Var 1 X.domain) (Var 0 X.domain))

let instance_controls
  (rho:V.environment (TR.carrier X.uninterpreted) (S.signature X.schema) [X.domain; X.domain])
  : Lemma (
    let original = TR.standard X.uninterpreted X.schema X.symbols in
    let extended = Model.override X.schema (TR.booleans X.uninterpreted)
      (SR.root_scalars X.uninterpreted) original X.inputs formula definition in
    Sub.substitute [argument] body == Some result /\
    Sub.substitute [argument] body <> Some captured /\
    T.evaluate_at X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended [X.domain; X.domain] rho (App X.symbol [argument]) ==
    T.evaluate_at X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended [X.domain; X.domain] rho result) =
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  let extended = Model.override X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) original X.inputs formula definition in
  assert_norm (Sub.substitute [argument] body == Some result);
  assert_norm (Sub.substitute [argument] body <> Some captured);
  assert_norm (Scope.scoped [X.domain; X.domain] argument);
  TR.lemma_standard_root X.uninterpreted X.schema X.symbols;
  Root.lemma_forall_model X.uninterpreted X.schema original;
  Model.lemma_definition X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    original X.inputs formula definition;
  Model.lemma_quantification X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    original X.inputs formula definition;
  Instance.lemma_instance X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    extended X.inputs formula X.domain definition [X.domain; X.domain] rho argument result
