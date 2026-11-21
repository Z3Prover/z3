module Z3IndependentDefinitionEquivalenceTests

open Z3AstTheory
module X = Z3IndependentDefinitionModelTests
module I = Z3IndependentDefinitionInstanceTests
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module Root = Z3SortedRootDocument
module Model = Z3IndependentDefinitionModel
module Scope = Z3ExprScope
module E = Z3IndependentDefinitionEquivalence

let named = App X.symbol [I.argument]
let wrap (e:expr) = Quantifier Forall_k [X.domain] bool_sort (R.mk_not_expr e)
let lhs = wrap named
let rhs = wrap I.result

let matcher_controls () : Lemma (
  E.equivalent 3 I.definition lhs rhs /\
  E.equivalent 3 I.definition rhs lhs /\
  not (E.equivalent 2 I.definition lhs rhs) /\
  not (E.equivalent 3 I.definition lhs (wrap I.captured)) /\
  not (E.equivalent 3 I.definition (wrap (App X.other_symbol [I.argument])) rhs) /\
  not (E.equivalent 3 I.definition (wrap (App X.symbol [Var 1 bool_sort])) rhs) /\
  not (E.equivalent 3 I.definition lhs (Quantifier Exists_k [X.domain] bool_sort (R.mk_not_expr I.result))) /\
  E.equivalent 0 I.definition lhs lhs) =
  assert_norm (E.equivalent 3 I.definition lhs rhs);
  assert_norm (E.equivalent 3 I.definition rhs lhs);
  assert_norm (not (E.equivalent 2 I.definition lhs rhs));
  assert_norm (not (E.equivalent 3 I.definition lhs (wrap I.captured)));
  assert_norm (not (E.equivalent 3 I.definition (wrap (App X.other_symbol [I.argument])) rhs));
  assert_norm (not (E.equivalent 3 I.definition (wrap (App X.symbol [Var 1 bool_sort])) rhs));
  assert_norm (not (E.equivalent 3 I.definition lhs (Quantifier Exists_k [X.domain] bool_sort (R.mk_not_expr I.result))));
  assert_norm (E.equivalent 0 I.definition lhs lhs)

let semantic_control
  (rho:V.environment (TR.carrier X.uninterpreted) (S.signature X.schema) [X.domain])
  : Lemma (
    let original = TR.standard X.uninterpreted X.schema X.symbols in
    let extended = Model.override X.schema (TR.booleans X.uninterpreted)
      (SR.root_scalars X.uninterpreted) original X.inputs I.formula X.domain I.definition in
    T.evaluate_at X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended [X.domain] rho lhs ==
    T.evaluate_at X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
      extended [X.domain] rho rhs) =
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  let extended = Model.override X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) original X.inputs I.formula X.domain I.definition in
  matcher_controls ();
  assert_norm (Scope.scoped [X.domain] lhs /\ Scope.scoped [X.domain] rhs);
  TR.lemma_standard_root X.uninterpreted X.schema X.symbols;
  Root.lemma_forall_model X.uninterpreted X.schema original;
  Model.lemma_definition X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    original X.inputs I.formula X.domain I.definition;
  Model.lemma_quantification X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    original X.inputs I.formula X.domain I.definition;
  E.lemma_equivalent X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    extended X.inputs I.formula X.domain I.definition [X.domain] rho 3 lhs rhs
