module Z3IndependentDefinitionNnfTests

open Z3AstTheory
module X = Z3IndependentDefinitionModelTests
module I = Z3IndependentDefinitionInstanceTests
module ET = Z3IndependentDefinitionEquivalenceTests
module CT = Z3IndependentDefinitionContextEquivalenceTests
module R = Z3ClauseSyntax
module O = Z3ObservationalSyntax
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module Root = Z3SortedRootDocument
module Model = Z3IndependentDefinitionModel
module Context = Z3IndependentDefinitionContext
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module N = Z3IndependentDefinitionNnf

let lhs = Quantifier Forall_k [X.domain] bool_sort ET.lhs
let rhs = Quantifier Forall_k [X.domain] bool_sort ET.rhs
let captured = Quantifier Forall_k [X.domain] bool_sort (ET.wrap I.captured)
let certificate (name:string) : U.binder_certificate = {
  U.binder_entries = [
    { U.binder_name = name; binder_formula = O.mk_oeq_expr lhs rhs;
      binder_premises = []; binder_sorts = None }
  ];
  binder_root = 0;
}
let entry (name:string) : P.entry = {
  P.rule = U.QuantifierIntroduction (certificate name);
  formula = O.mk_oeq_expr lhs rhs;
  premise_ids = [];
}
let eq_entry : P.entry = { entry "nnf-neg" with P.formula = R.mk_eq_expr lhs rhs }
let rec repeat (n:nat) : Tot (list (Context.item X.schema X.inputs)) (decreases n) =
  if n = 0 then [] else CT.item :: repeat (n - 1)
let rec oversized (n:nat) : Tot expr (decreases n) =
  if n = 0 then R.true_expr
  else let e = oversized (n - 1) in R.mk_eq_expr e e

let candidate_controls () : Lemma (
  N.candidate X.schema X.inputs [CT.item] (entry "nnf-pos") == Some (U.Observational lhs rhs) /\
  N.candidate X.schema X.inputs [CT.item] eq_entry == Some (U.Equal lhs rhs) /\
  N.candidate X.schema X.inputs [] (entry "nnf-pos") == None /\
  N.candidate X.schema X.inputs [CT.item] (entry "quant-intro") == None /\
  N.candidate X.schema X.inputs [CT.item] { entry "nnf-pos" with P.premise_ids = [0] } == None /\
  N.candidate X.schema X.inputs [CT.item] { entry "nnf-pos" with P.formula = O.mk_oeq_expr lhs captured } == None /\
  N.candidate X.schema X.inputs [CT.item] { entry "nnf-pos" with P.formula = O.mk_oeq_expr ET.lhs ET.rhs } == None /\
  N.candidate X.schema X.inputs [CT.item] { entry "nnf-pos" with P.formula = oversized 10 } == None /\
  N.candidate X.schema X.inputs (repeat 17) (entry "nnf-pos") == None) =
  assert_norm (N.candidate X.schema X.inputs [CT.item] (entry "nnf-pos") == Some (U.Observational lhs rhs));
  assert_norm (N.candidate X.schema X.inputs [CT.item] eq_entry == Some (U.Equal lhs rhs));
  assert_norm (N.candidate X.schema X.inputs [] (entry "nnf-pos") == None);
  assert_norm (N.candidate X.schema X.inputs [CT.item] (entry "quant-intro") == None);
  assert_norm (N.candidate X.schema X.inputs [CT.item] { entry "nnf-pos" with P.premise_ids = [0] } == None);
  assert_norm (N.candidate X.schema X.inputs [CT.item] { entry "nnf-pos" with P.formula = O.mk_oeq_expr lhs captured } == None);
  assert_norm (N.candidate X.schema X.inputs [CT.item] { entry "nnf-pos" with P.formula = O.mk_oeq_expr ET.lhs ET.rhs } == None);
  assert_norm (N.candidate X.schema X.inputs [CT.item] { entry "nnf-pos" with P.formula = oversized 10 } == None);
  assert_norm (N.candidate X.schema X.inputs (repeat 17) (entry "nnf-pos") == None)

let semantic_control () : Lemma (
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  let extended = Model.override X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) original X.inputs I.formula X.domain I.definition in
  T.truth X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    extended (R.mk_eq_expr lhs rhs)) =
  let original = TR.standard X.uninterpreted X.schema X.symbols in
  let extended = Model.override X.schema (TR.booleans X.uninterpreted)
    (SR.root_scalars X.uninterpreted) original X.inputs I.formula X.domain I.definition in
  candidate_controls ();
  TR.lemma_standard_root X.uninterpreted X.schema X.symbols;
  Root.lemma_forall_model X.uninterpreted X.schema original;
  Model.lemma_definition X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    original X.inputs I.formula X.domain I.definition;
  Model.lemma_quantification X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    original X.inputs I.formula X.domain I.definition;
  N.lemma_candidate X.schema (TR.booleans X.uninterpreted) (SR.root_scalars X.uninterpreted)
    extended X.inputs [CT.item] (entry "nnf-pos") (U.Observational lhs rhs)
