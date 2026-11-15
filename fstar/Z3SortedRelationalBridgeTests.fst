module Z3SortedRelationalBridgeTests

open Z3AstTheory
module U = Z3UnifiedProof
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module SC = Z3SortedRelational
module Bridge = Z3SortedRelationalBridge
module Cases = Z3SortedRelationalTests
module CS = Z3ClausalSemantics

let default_conditional_dispatch (#base:sort -> Type0) (s:S.checked_schema)
                                 (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                                 (other:V.interpretation base (S.signature s))
                                 (rho:V.environment base (S.signature s) Cases.scope)
  : Lemma (requires SC.facts_hold s bc eq other Cases.scope rho Cases.conditional_node.U.premises)
          (ensures SC.fact_holds s bc eq other Cases.scope rho Cases.conditional_fact /\
                   (CS.conj_holds (T.truth_at s bc eq other Cases.scope rho)
                      [Cases.p; Cases.z; Cases.q] ==>
                    T.observations_agree_at s bc eq other Cases.scope rho Cases.p Cases.z)) =
  assert_norm (U.check_node_with_membership [] false [] (fun _ -> false) Cases.conditional_node ==
               Some (Cases.conditional_fact, 0));
  Bridge.lemma_default_fact_node s bc eq other Cases.scope rho [] false [] (fun _ -> false)
    Cases.conditional_node Cases.conditional_fact
