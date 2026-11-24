module Z3IndependentDefinitionContextTests

open Z3AstTheory
module X = Z3IndependentDefinitionModelTests
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module R = Z3ClauseSyntax
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module Root = Z3SortedRootDocument
module Pair = Z3IndependentDefinitionPair
module Model = Z3IndependentDefinitionModel
module Context = Z3IndependentDefinitionContext
module Scope = Z3ExprScope
module Dependent = Z3SortedDependentSkolem
module RL = Z3SortedReal
module DV = Z3SortedIntDivision
module RR = Z3SortedRealRoot
module DR = Z3SortedDivisionRoot
module DefinitionRoot = Z3IndependentDefinitionRoot
module NativeDatatype = Z3DatatypeNativeModelTests

let old_item : Context.item X.schema X.inputs = {
  Context.formula = X.formula;
  Context.definition = X.definition;
}

let scalar_item : Context.item X.schema X.inputs = {
  Context.formula = X.scalar_formula;
  Context.definition = X.scalar_definition;
}

let dependent_body = App X.symbol [Var 0 X.domain]
let raw_new : D.definition = {
  D.symbol = X.other_symbol; variables = [0]; body = dependent_body;
}

let pair (symbol:func_decl) (body:expr) : expr =
  let name = App symbol [Var 0 X.domain] in
  let left = [R.mk_not_expr name; body] in
  let right = [name; R.mk_not_expr body] in
  let args = [
    Quantifier Forall_k [X.domain] bool_sort (App (R.or_decl left) left);
    Quantifier Forall_k [X.domain] bool_sort (App (R.or_decl right) right)
  ] in
  App (R.and_decl args) args

let new_formula = pair X.other_symbol dependent_body

let new_definition : Model.definition X.schema X.inputs new_formula =
  assert_norm (Dependent.function_safe X.schema X.other_symbol);
  assert_norm (D.make_definition [X.domain] (App X.other_symbol [Var 0 X.domain]) dependent_body ==
    Some raw_new);
  assert_norm (D.fresh [raw_new] dependent_body /\ D.fresh_args [raw_new] X.inputs);
  assert_norm (Scope.scoped [] new_formula);
  let paired = Pair.pair X.domain raw_new in
  assert (paired == new_formula);
  let accepted = Pair.valid X.schema X.inputs new_formula raw_new in
  assert (accepted);
  raw_new

let new_item : Context.item X.schema X.inputs = {
  Context.formula = new_formula;
  Context.definition = new_definition;
}

let cyclic_body = App X.other_symbol [Var 0 X.domain]
let raw_cyclic : D.definition = {
  D.symbol = X.symbol; variables = [0]; body = cyclic_body;
}
let cyclic_formula = pair X.symbol cyclic_body

let cyclic_definition : Model.definition X.schema X.inputs cyclic_formula =
  assert_norm (Dependent.function_safe X.schema X.symbol);
  assert_norm (D.make_definition [X.domain] (App X.symbol [Var 0 X.domain]) cyclic_body ==
    Some raw_cyclic);
  assert_norm (D.fresh [raw_cyclic] cyclic_body /\ D.fresh_args [raw_cyclic] X.inputs);
  assert_norm (Scope.scoped [] cyclic_formula);
  let paired = Pair.pair X.domain raw_cyclic in
  assert (paired == cyclic_formula);
  let accepted = Pair.valid X.schema X.inputs cyclic_formula raw_cyclic in
  assert (accepted);
  raw_cyclic

let cyclic_item : Context.item X.schema X.inputs = {
  Context.formula = cyclic_formula;
  Context.definition = cyclic_definition;
}

let ordering_controls ()
  : Lemma (Context.ordered X.schema X.inputs [new_item; old_item] /\
           not (Context.ordered X.schema X.inputs [old_item; new_item]) /\
           not (Context.ordered X.schema X.inputs [old_item; old_item]) /\
           not (Context.ordered X.schema X.inputs [new_item; cyclic_item]) /\
           not (Context.ordered X.schema X.inputs [cyclic_item; new_item])) =
  assert_norm (Context.ordered X.schema X.inputs [new_item; old_item]);
  assert_norm (not (Context.ordered X.schema X.inputs [old_item; new_item]));
  assert_norm (not (Context.ordered X.schema X.inputs [old_item; old_item]));
  assert_norm (not (Context.ordered X.schema X.inputs [new_item; cyclic_item]));
  assert_norm (not (Context.ordered X.schema X.inputs [cyclic_item; new_item]))

let dependency_order_controls ()
  : Lemma (
    (match Context.dependency_order X.schema X.inputs [old_item; new_item] with
     | Some items ->
       Context.ordered X.schema X.inputs items /\
       Context.formulas X.schema X.inputs items == [new_formula; X.formula]
     | None -> false) /\
    Context.dependency_order X.schema X.inputs [new_item; cyclic_item] == None /\
    Context.dependency_order X.schema X.inputs [old_item; old_item] == None) =
  assert_norm (match Context.dependency_order X.schema X.inputs [old_item; new_item] with
    | Some items ->
      Context.ordered X.schema X.inputs items /\
      Context.formulas X.schema X.inputs items == [new_formula; X.formula]
    | None -> false);
  assert_norm (Context.dependency_order X.schema X.inputs [new_item; cyclic_item] == None);
  assert_norm (Context.dependency_order X.schema X.inputs [old_item; old_item] == None)

let inhabited_dependent_context ()
  : Lemma (
    let original = TR.standard X.uninterpreted X.schema X.symbols in
    let items = [new_item; old_item] in
    let extended = Context.build X.schema (TR.booleans X.uninterpreted)
      (SR.root_scalars X.uninterpreted) X.inputs items original in
    T.truths X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended (Context.formulas X.schema X.inputs items) /\
    T.truths X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended X.inputs ==
    T.truths X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      original X.inputs) =
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  TR.lemma_standard_root X.uninterpreted X.schema X.symbols;
  Root.lemma_forall_model X.uninterpreted X.schema original;
  ordering_controls ();
  Context.lemma_build_context X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) X.inputs [new_item; old_item] original;
  Context.lemma_build_inputs X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) X.inputs [new_item; old_item] original

let inhabited_arithmetic_laws ()
  : Lemma (
    let original = TR.standard X.uninterpreted X.schema X.symbols in
    let extended = Context.build X.schema (TR.booleans X.uninterpreted)
      (SR.root_scalars X.uninterpreted) X.inputs [new_item; old_item] original in
    RL.real_laws X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended (RR.root_reals X.uninterpreted) /\
    DV.division_laws X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended) =
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  assert_norm (RL.real_primitive X.schema);
  DR.lemma_standard_joint_root X.uninterpreted X.schema X.symbols;
  Context.lemma_build_real X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) X.inputs [new_item; old_item]
    original (RR.root_reals X.uninterpreted);
  Context.lemma_build_division X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) X.inputs [new_item; old_item] original

let inhabited_root_context ()
  : Lemma (
    let original = TR.standard X.uninterpreted X.schema X.symbols in
    let extended = Context.build X.schema (TR.booleans X.uninterpreted)
      (SR.root_scalars X.uninterpreted) X.inputs [new_item; old_item] original in
    TR.root_model X.uninterpreted X.schema extended) =
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  TR.lemma_standard_root X.uninterpreted X.schema X.symbols;
  DefinitionRoot.lemma_build_root X.uninterpreted X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) X.inputs [new_item; old_item] original

let inhabited_scalar_context ()
  : Lemma (
    let original = TR.standard X.uninterpreted X.schema X.symbols in
    let extended = Context.build X.schema (TR.booleans X.uninterpreted)
      (SR.root_scalars X.uninterpreted) X.inputs [scalar_item] original in
    T.truths X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended [X.scalar_formula]) =
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  assert_norm (Context.ordered X.schema X.inputs [scalar_item]);
  TR.lemma_standard_root X.uninterpreted X.schema X.symbols;
  Root.lemma_forall_model X.uninterpreted X.schema original;
  Context.lemma_build_context X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) X.inputs [scalar_item] original

let datatype_definition : Model.definition NativeDatatype.schema X.inputs X.formula =
  assert_norm (Dependent.function_safe NativeDatatype.schema X.symbol);
  assert_norm (D.make_definition [X.domain] (App X.symbol [Var 0 X.domain]) R.true_expr ==
    Some X.raw_definition);
  assert_norm (D.fresh [X.raw_definition] R.true_expr /\ D.fresh_args [X.raw_definition] X.inputs);
  assert_norm (Scope.scoped [] X.formula);
  let paired = Pair.pair X.domain X.raw_definition in
  assert (paired == X.formula);
  let accepted = Pair.valid NativeDatatype.schema X.inputs X.formula X.raw_definition in
  assert (accepted);
  X.raw_definition

let datatype_item : Context.item NativeDatatype.schema X.inputs = {
  Context.formula = X.formula;
  Context.definition = datatype_definition;
}

noextract
let datatype_symbols : TR.symbols X.uninterpreted NativeDatatype.schema = {
  TR.apply = (fun f _ -> S.value_inhabitant NativeDatatype.schema
    (TR.default_value X.uninterpreted) f.range);
  TR.lambda = (fun bound t _ -> S.value_inhabitant NativeDatatype.schema
    (TR.default_value X.uninterpreted) (ArraySort bound t));
}

let datatype_root_context ()
  : Lemma (
    let original = TR.standard X.uninterpreted NativeDatatype.schema datatype_symbols in
    let extended = Context.build NativeDatatype.schema (TR.booleans X.uninterpreted)
      (SR.root_scalars X.uninterpreted) X.inputs [datatype_item] original in
    TR.root_model X.uninterpreted NativeDatatype.schema extended /\
    not (Dependent.function_safe NativeDatatype.schema NativeDatatype.branch_c) /\
    not (Dependent.function_safe NativeDatatype.schema NativeDatatype.branch_tester) /\
    not (Dependent.function_safe NativeDatatype.schema NativeDatatype.children)) =
  let original = TR.standard X.uninterpreted NativeDatatype.schema datatype_symbols in
  assert_norm (not (Dependent.function_safe NativeDatatype.schema NativeDatatype.branch_c));
  assert_norm (not (Dependent.function_safe NativeDatatype.schema NativeDatatype.branch_tester));
  assert_norm (not (Dependent.function_safe NativeDatatype.schema NativeDatatype.children));
  TR.lemma_standard_root X.uninterpreted NativeDatatype.schema datatype_symbols;
  DefinitionRoot.lemma_build_root X.uninterpreted NativeDatatype.schema
    (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    X.inputs [datatype_item] original
