module Z3SortedLeafFacts

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module Node = Z3UnifiedNode
module SK = Z3SkolemSyntax
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module SC = Z3SortedRelational
module CS = Z3ClausalSemantics

let lemma_checked_leaf (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (check_step:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                       (check_theory:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                       (check_binder:list SK.definition -> list U.judgment -> U.binder_certificate ->
                                     U.judgment -> Tot bool)
                       (skolems:list SK.definition) (strict:bool)
                       (assertions:list U.judgment) (contains:U.judgment -> bool)
                       (node:U.proof_node) (fact:U.checked_fact)
  : Lemma (requires (node.U.kind == U.Asserted \/ node.U.kind == U.Hypothesis) /\
                    (node.U.kind == U.Asserted /\ contains node.U.conclusion ==>
                     SC.judgment_holds s bc eq other scope rho node.U.conclusion) /\
                    Node.check_node_with_membership check_step check_theory check_binder
                      skolems strict assertions contains node == Some (fact, 0))
          (ensures fact.U.conclusion == node.U.conclusion /\
                   SC.fact_holds s bc eq other scope rho fact) =
  if node.U.kind = U.Hypothesis &&
     CS.conj_holds (T.truth_at s bc eq other scope rho) fact.U.hypotheses then
    match node.U.conclusion with
    | U.Equal a b -> T.lemma_equality_at s bc eq other scope rho a b
    | _ -> ()
