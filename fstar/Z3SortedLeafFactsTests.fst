module Z3SortedLeafFactsTests

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module Node = Z3UnifiedNode
module Leaf = Z3SortedLeafFacts
module SC = Z3SortedRelational
module Cases = Z3SortedRelationalTests
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics

let hypothesis : U.proof_node = {
  U.kind = U.Hypothesis;
  U.conclusion = U.Equal Cases.p Cases.q;
  U.premises = [];
}

let hypothesis_fact : U.checked_fact = {
  U.conclusion = U.Equal Cases.p Cases.q;
  U.hypotheses = [R.mk_eq_expr Cases.p Cases.q];
}

let unscoped_hypothesis (#base:sort -> Type0) (s:S.checked_schema)
                        (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                        (other:V.interpretation base (S.signature s))
                        (rho:V.environment base (S.signature s) [])
  : Lemma (SC.fact_holds s bc eq other [] rho hypothesis_fact) =
  assert_norm (Node.check_node_with_membership Cases.core_check Cases.rejected_theory Cases.rejected_binder
                 [] false [] (fun _ -> false) hypothesis == Some (hypothesis_fact, 0));
  Leaf.lemma_checked_leaf s bc eq other [] rho Cases.core_check Cases.rejected_theory Cases.rejected_binder
    [] false [] (fun _ -> false) hypothesis hypothesis_fact

let asserted : U.proof_node = {
  U.kind = U.Asserted;
  U.conclusion = U.Holds Cases.p;
  U.premises = [];
}

let asserted_fact : U.checked_fact = { U.conclusion = U.Holds Cases.p; U.hypotheses = [] }
let contains (j:U.judgment) = j = U.Holds Cases.p

let asserted_input (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (rho:V.environment base (S.signature s) Cases.scope)
  : Lemma (requires T.truth_at s bc eq other Cases.scope rho Cases.p)
          (ensures SC.fact_holds s bc eq other Cases.scope rho asserted_fact) =
  assert_norm (Node.check_node_with_membership Cases.core_check Cases.rejected_theory Cases.rejected_binder
                 [] false [U.Holds Cases.p] contains asserted == Some (asserted_fact, 0));
  Leaf.lemma_checked_leaf s bc eq other Cases.scope rho Cases.core_check Cases.rejected_theory
    Cases.rejected_binder [] false [U.Holds Cases.p] contains asserted asserted_fact
