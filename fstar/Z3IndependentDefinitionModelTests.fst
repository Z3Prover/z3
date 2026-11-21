module Z3IndependentDefinitionModelTests

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module R = Z3ClauseSyntax
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module Root = Z3SortedRootDocument
module Pair = Z3IndependentDefinitionPair
module Model = Z3IndependentDefinitionModel
module B = Z3BoundedBoolEquiv
module Scope = Z3ExprScope
module Dependent = Z3SortedDependentSkolem
module V = Z3DatatypeValue

let schema : S.checked_schema =
  let s = { S.sorts = []; cases = [] } in
  assert_norm (S.valid s);
  s

let domain = BaseSort "U"
let symbol = {
  decl_name = "fresh"; domain = [domain]; range = bool_sort; interp = None; int_params = [];
}
let other_symbol = {
  decl_name = "other"; domain = [domain]; range = bool_sort; interp = None; int_params = [];
}
let raw_definition : D.definition = {
  D.symbol = symbol; variables = [0]; body = R.true_expr;
}
let inputs = [R.true_expr]
let formula =
  let name = App symbol [Var 0 domain] in
  let left = [R.mk_not_expr name; R.true_expr] in
  let right = [name; R.mk_not_expr R.true_expr] in
  let args = [
    Quantifier Forall_k [domain] bool_sort (App (R.or_decl left) left);
    Quantifier Forall_k [domain] bool_sort (App (R.or_decl right) right)
  ] in
  App (R.and_decl args) args

let definition : Model.definition schema inputs formula domain =
  assert_norm (Dependent.function_safe schema symbol);
  assert_norm (D.make_definition [domain] (App symbol [Var 0 domain]) R.true_expr ==
    Some raw_definition);
  assert_norm (D.fresh [raw_definition] R.true_expr /\ D.fresh_args [raw_definition] inputs);
  assert_norm (Scope.scoped [] formula);
  let paired = Pair.pair domain raw_definition in
  assert (paired == formula);
  let accepted = Pair.valid schema inputs formula raw_definition in
  assert (accepted);
  raw_definition

let uninterpreted : TR.uninterpreted = {
  TR.sort_carrier = (fun _ -> unit);
  TR.inhabitant = (fun _ -> ());
}

noextract
let symbols : TR.symbols uninterpreted schema = {
  TR.apply = (fun f _ -> S.value_inhabitant schema (TR.default_value uninterpreted) f.range);
  TR.lambda = (fun bound t _ ->
    S.value_inhabitant schema (TR.default_value uninterpreted) (ArraySort bound t));
}

let inhabited_extension ()
  : Lemma (
    let original = TR.standard uninterpreted schema symbols in
    let extended = Model.override schema (TR.booleans uninterpreted)
      (SR.root_scalars uninterpreted) original inputs formula domain definition in
    T.truth schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted) extended formula /\
    T.truths schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted) extended inputs) =
  let original = TR.standard uninterpreted schema symbols in
  TR.lemma_standard_root uninterpreted schema symbols;
  Root.lemma_forall_model uninterpreted schema original;
  Model.lemma_definition schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original inputs formula domain definition;
  Model.lemma_inputs schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original inputs formula domain definition;
  T.lemma_cut schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original 1 R.true_expr;
  assert_norm (T.cut 1 R.true_expr == B.Bool true)

let pointwise_and_other_symbol (rho:V.environment (TR.carrier uninterpreted) (S.signature schema) [domain])
  : Lemma (
    let original = TR.standard uninterpreted schema symbols in
    let extended = Model.override schema (TR.booleans uninterpreted)
      (SR.root_scalars uninterpreted) original inputs formula domain definition in
    T.truth_at schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
      extended [domain] rho (App symbol [Var 0 domain]) /\
    T.evaluate_at schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
      extended [domain] rho (App other_symbol [Var 0 domain]) ==
    T.evaluate_at schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
      original [domain] rho (App other_symbol [Var 0 domain])) =
  let original = TR.standard uninterpreted schema symbols in
  let extended = Model.override schema (TR.booleans uninterpreted)
    (SR.root_scalars uninterpreted) original inputs formula domain definition in
  assert_norm (Scope.scoped [domain] (App other_symbol [Var 0 domain]));
  assert_norm (D.fresh [raw_definition] (App other_symbol [Var 0 domain]));
  Model.lemma_fresh schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original inputs formula domain definition [domain] rho (App other_symbol [Var 0 domain]);
  Model.lemma_pointwise schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original inputs formula domain definition rho;
  T.lemma_cut_with_boundaries_at schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    extended [domain] rho [] 1 R.true_expr;
  assert_norm (T.cut 1 R.true_expr == B.Bool true)
