module Z3IndependentDefinitionContextEquivalenceTests

open Z3AstTheory
module X = Z3IndependentDefinitionModelTests
module I = Z3IndependentDefinitionInstanceTests
module Test = Z3IndependentDefinitionEquivalenceTests
module CT = Z3IndependentDefinitionContextTests
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module Root = Z3SortedRootDocument
module Model = Z3IndependentDefinitionModel
module Context = Z3IndependentDefinitionContext
module Eq = Z3IndependentDefinitionContextEquivalence
module Scope = Z3ExprScope

let item : Context.item X.schema X.inputs = {
  Context.formula = I.formula;
  Context.definition = I.definition;
}

let selection_controls () : Lemma (
  not (Eq.matches X.schema X.inputs [] 3 Test.lhs Test.rhs) /\
  not (Eq.matches X.schema X.inputs [CT.new_item] 3 Test.lhs Test.rhs) /\
  Eq.matches X.schema X.inputs [CT.new_item; item] 3 Test.lhs Test.rhs /\
  not (Eq.matches X.schema X.inputs [item] 2 Test.lhs Test.rhs)) =
  assert_norm (not (Eq.matches X.schema X.inputs [] 3 Test.lhs Test.rhs));
  assert_norm (not (Eq.matches X.schema X.inputs [CT.new_item] 3 Test.lhs Test.rhs));
  assert_norm (Eq.matches X.schema X.inputs [CT.new_item; item] 3 Test.lhs Test.rhs);
  assert_norm (not (Eq.matches X.schema X.inputs [item] 2 Test.lhs Test.rhs))

let semantic_control
  (rho:V.environment (TR.carrier X.uninterpreted) (S.signature X.schema) [X.domain])
  : Lemma (
    let original = TR.standard X.uninterpreted X.schema X.symbols in
    let extended = Model.override X.schema (TR.booleans X.uninterpreted)
      (SR.root_scalars X.uninterpreted) original X.inputs I.formula I.definition in
    T.evaluate_at X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended [X.domain] rho Test.lhs ==
    T.evaluate_at X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended [X.domain] rho Test.rhs) =
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  let extended = Model.override X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) original X.inputs I.formula I.definition in
  assert_norm (Eq.matches X.schema X.inputs [item] 3 Test.lhs Test.rhs);
  assert_norm (Scope.scoped [X.domain] Test.lhs /\ Scope.scoped [X.domain] Test.rhs);
  TR.lemma_standard_root X.uninterpreted X.schema X.symbols;
  Root.lemma_forall_model X.uninterpreted X.schema original;
  Model.lemma_definition X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    original X.inputs I.formula I.definition;
  Model.lemma_quantification X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    original X.inputs I.formula I.definition;
  Eq.lemma_matches X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    extended X.inputs [item] [X.domain] rho 3 Test.lhs Test.rhs
