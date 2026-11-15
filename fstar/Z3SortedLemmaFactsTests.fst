module Z3SortedLemmaFactsTests

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module Node = Z3UnifiedNode
module SC = Z3SortedRelational
module Lemma = Z3SortedLemmaFacts
module Cases = Z3SortedRelationalTests
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics

let neg_p = R.mk_not_expr Cases.p
let disj = App (R.or_decl [neg_p; Cases.q]) [neg_p; Cases.q]
let false_fact : U.checked_fact = {
  U.conclusion = U.Holds R.false_expr;
  U.hypotheses = [Cases.p; Cases.z];
}
let node : U.proof_node = {
  U.kind = U.LemmaRule;
  U.conclusion = U.Holds disj;
  U.premises = [false_fact];
}
let result : U.checked_fact = {
  U.conclusion = U.Holds disj;
  U.hypotheses = [Cases.z];
}

let discharge (#base:sort -> Type0) (s:S.checked_schema)
              (bc:S.boolean_carrier base) (eq:T.scalar_model base)
              (other:V.interpretation base (S.signature s))
              (rho:V.environment base (S.signature s) Cases.scope)
  : Lemma (requires SC.fact_holds s bc eq other Cases.scope rho false_fact)
          (ensures SC.fact_holds s bc eq other Cases.scope rho result) =
  assert_norm (Node.check_node_with_membership Cases.core_check Cases.rejected_theory Cases.rejected_binder
                 [] false [] (fun _ -> false) node == Some (result, 0));
  Lemma.lemma_checked s bc eq other Cases.scope rho Cases.core_check Cases.rejected_theory
    Cases.rejected_binder [] false [] (fun _ -> false) node result disj
