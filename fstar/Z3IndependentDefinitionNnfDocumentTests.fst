module Z3IndependentDefinitionNnfDocumentTests

open Z3AstTheory
module X = Z3IndependentDefinitionModelTests
module CT = Z3IndependentDefinitionContextEquivalenceTests
module NT = Z3IndependentDefinitionNnfTests
module R = Z3ClauseSyntax
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module N = Z3IndependentDefinitionNnfDocument

let accepted = NT.entry "nnf-pos"
let rejected = { NT.entry "nnf-neg" with P.premise_ids = [0] }
let asserted : P.entry = { P.rule = U.Asserted; formula = R.false_expr; premise_ids = [] }

let collection_controls () : Lemma (
  N.collect X.schema X.inputs [CT.item] [accepted; rejected; asserted] ==
    ([R.mk_eq_expr NT.lhs NT.rhs], [{ accepted with P.rule = U.Asserted }; rejected; asserted]) /\
  N.collect X.schema X.inputs [] [accepted; asserted] == ([], [accepted; asserted]) /\
  N.collect X.schema X.inputs [CT.item] [NT.eq_entry; accepted] ==
    ([R.mk_eq_expr NT.lhs NT.rhs; R.mk_eq_expr NT.lhs NT.rhs],
     [{ NT.eq_entry with P.rule = U.Asserted }; { accepted with P.rule = U.Asserted }])) =
  assert_norm (N.collect X.schema X.inputs [CT.item] [accepted; rejected; asserted] ==
    ([R.mk_eq_expr NT.lhs NT.rhs], [{ accepted with P.rule = U.Asserted }; rejected; asserted]));
  assert_norm (N.collect X.schema X.inputs [] [accepted; asserted] == ([], [accepted; asserted]));
  assert_norm (N.collect X.schema X.inputs [CT.item] [NT.eq_entry; accepted] ==
    ([R.mk_eq_expr NT.lhs NT.rhs; R.mk_eq_expr NT.lhs NT.rhs],
     [{ NT.eq_entry with P.rule = U.Asserted }; { accepted with P.rule = U.Asserted }]))
