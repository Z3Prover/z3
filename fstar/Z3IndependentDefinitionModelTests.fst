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
module A = Z3ArraySyntax
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

let definition : Model.definition schema inputs formula =
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

let scalar_symbol = {
  decl_name = "fresh-scalar"; domain = []; range = domain; interp = None; int_params = [];
}
let scalar_then = {
  decl_name = "scalar-then"; domain = []; range = domain; interp = None; int_params = [];
}
let scalar_else = {
  decl_name = "scalar-else"; domain = []; range = domain; interp = None; int_params = [];
}
let scalar_body = App (A.term_ite_decl domain)
  [R.true_expr; App scalar_then []; App scalar_else []]
let scalar_raw : D.definition = { D.symbol = scalar_symbol; variables = []; body = scalar_body }
let scalar_formula =
  Pair.scalar_pair R.true_expr (App scalar_symbol []) (App scalar_then []) (App scalar_else [])
let scalar_definition : Model.definition schema inputs scalar_formula =
  assert_norm (Dependent.function_safe schema scalar_symbol);
  assert_norm (get_sort scalar_body == domain);
  assert_norm (D.fresh [scalar_raw] scalar_body);
  assert_norm (D.fresh_args [scalar_raw] inputs);
  assert_norm (Scope.scoped [] (App scalar_symbol []));
  assert_norm (Scope.scoped [] scalar_body);
  assert_norm (Scope.scoped [] scalar_formula);
  assert_norm (A.ite_parts scalar_body ==
    Some (R.true_expr, App scalar_then [], App scalar_else []));
  assert_norm (scalar_formula ==
    Pair.scalar_pair R.true_expr (App scalar_symbol []) (App scalar_then []) (App scalar_else []));
  let accepted = Pair.scalar_valid schema inputs scalar_formula scalar_raw in
  assert (accepted);
  scalar_raw

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
      (SR.root_scalars uninterpreted) original inputs formula definition in
    T.truth schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted) extended formula /\
    T.truths schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted) extended inputs) =
  let original = TR.standard uninterpreted schema symbols in
  TR.lemma_standard_root uninterpreted schema symbols;
  Root.lemma_forall_model uninterpreted schema original;
  Model.lemma_definition schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original inputs formula definition;
  Model.lemma_inputs schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original inputs formula definition;
  T.lemma_cut schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original 1 R.true_expr;
  assert_norm (T.cut 1 R.true_expr == B.Bool true)

let scalar_ite_extension ()
  : Lemma (
    let original = TR.standard uninterpreted schema symbols in
    let extended = Model.override schema (TR.booleans uninterpreted)
      (SR.root_scalars uninterpreted) original inputs scalar_formula scalar_definition in
    T.truth schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
      extended scalar_formula) =
  let original = TR.standard uninterpreted schema symbols in
  let extended = Model.override schema (TR.booleans uninterpreted)
    (SR.root_scalars uninterpreted) original inputs scalar_formula scalar_definition in
  TR.lemma_standard_root uninterpreted schema symbols;
  Root.lemma_forall_model uninterpreted schema original;
  Model.lemma_definition schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original inputs scalar_formula scalar_definition

let pointwise_and_other_symbol (rho:V.environment (TR.carrier uninterpreted) (S.signature schema) [domain])
  : Lemma (
    let original = TR.standard uninterpreted schema symbols in
    let extended = Model.override schema (TR.booleans uninterpreted)
      (SR.root_scalars uninterpreted) original inputs formula definition in
    T.truth_at schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
      extended [domain] rho (App symbol [Var 0 domain]) /\
    T.evaluate_at schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
      extended [domain] rho (App other_symbol [Var 0 domain]) ==
    T.evaluate_at schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
      original [domain] rho (App other_symbol [Var 0 domain])) =
  let original = TR.standard uninterpreted schema symbols in
  let extended = Model.override schema (TR.booleans uninterpreted)
    (SR.root_scalars uninterpreted) original inputs formula definition in
  assert_norm (Scope.scoped [domain] (App other_symbol [Var 0 domain]));
  assert_norm (D.fresh [raw_definition] (App other_symbol [Var 0 domain]));
  Model.lemma_fresh schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original inputs formula definition [domain] rho (App other_symbol [Var 0 domain]);
  Model.lemma_pointwise schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    original inputs formula domain definition rho;
  T.lemma_cut_with_boundaries_at schema (TR.booleans uninterpreted) (SR.root_scalars uninterpreted)
    extended [domain] rho [] 1 R.true_expr;
  assert_norm (T.cut 1 R.true_expr == B.Bool true)
