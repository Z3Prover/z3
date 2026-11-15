module Z3SortedModusPonensTests

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module R = Z3ClauseSyntax
module Node = Z3UnifiedNode
module Sorted = Z3SortedModusPonens
module SC = Z3SortedRelational
module Cases = Z3SortedRelationalTests
module SyntaxCases = Z3ModusPonensSyntaxTests
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics

let premise : U.checked_fact = { U.conclusion = U.Holds Cases.p; U.hypotheses = [Cases.z] }
let implication : U.checked_fact = {
  U.conclusion = U.Holds SyntaxCases.implication; U.hypotheses = [Cases.z]
}
let equation : U.checked_fact = { U.conclusion = U.Equal Cases.p Cases.q; U.hypotheses = [Cases.z] }
let observation : U.checked_fact = { U.conclusion = U.Observational Cases.p Cases.q; U.hypotheses = [Cases.z] }
let result : U.checked_fact = { U.conclusion = U.Holds Cases.q; U.hypotheses = [Cases.z] }

let imp_node : U.proof_node = { U.kind = U.ModusPonens; U.conclusion = result.U.conclusion;
                               U.premises = [premise; implication] }
let eq_node : U.proof_node = { U.kind = U.ModusPonens; U.conclusion = result.U.conclusion;
                              U.premises = [premise; equation] }
let obs_node : U.proof_node = { U.kind = U.ObservationalMP; U.conclusion = result.U.conclusion;
                               U.premises = [premise; observation] }

let mp_check (kind:U.rule) (concl:U.judgment) (premises:list U.judgment) : bool =
  Z3ModusPonensSyntax.step kind concl premises

let conditional_steps (#base:sort -> Type0) (s:S.checked_schema)
                      (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                      (other:V.interpretation base (S.signature s))
                      (rho:V.environment base (S.signature s) Cases.scope)
  : Lemma (requires SC.facts_hold s bc eq other Cases.scope rho imp_node.U.premises /\
                    SC.facts_hold s bc eq other Cases.scope rho eq_node.U.premises /\
                    SC.facts_hold s bc eq other Cases.scope rho obs_node.U.premises)
          (ensures SC.fact_holds s bc eq other Cases.scope rho result) =
  assert_norm (Node.check_node_with_membership mp_check Cases.rejected_theory Cases.rejected_binder
                 [] false [] (fun _ -> false) imp_node == Some (result, 0) /\
               Node.check_node_with_membership mp_check Cases.rejected_theory Cases.rejected_binder
                 [] false [] (fun _ -> false) eq_node == Some (result, 0) /\
               Node.check_node_with_membership mp_check Cases.rejected_theory Cases.rejected_binder
                 [] false [] (fun _ -> false) obs_node == Some (result, 0));
  Sorted.lemma_checked_fact s bc eq other Cases.scope rho mp_check Cases.rejected_theory
    Cases.rejected_binder [] false [] (fun _ -> false) imp_node result Cases.q;
  Sorted.lemma_checked_fact s bc eq other Cases.scope rho mp_check Cases.rejected_theory
    Cases.rejected_binder [] false [] (fun _ -> false) eq_node result Cases.q;
  Sorted.lemma_checked_fact s bc eq other Cases.scope rho mp_check Cases.rejected_theory
    Cases.rejected_binder [] false [] (fun _ -> false) obs_node result Cases.q
