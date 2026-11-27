module Z3SortedModusPonensBridge

open Z3AstTheory
module U = Z3UnifiedProof
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module SC = Z3SortedRelational
module SH = Z3SortedHypothesisSemantics
module Sorted = Z3SortedModusPonens
module SK = Z3SkolemSyntax

let lemma_default_fact (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (skolems:list SK.definition) (strict:bool)
                       (assertions:list U.judgment) (contains:U.judgment -> bool)
                       (node:U.proof_node) (fact:U.checked_fact) (target:expr)
  : Lemma (requires (node.U.kind == U.ModusPonens \/ node.U.kind == U.ObservationalMP) /\
                    U.proposition node.U.conclusion == Some target /\ SH.valid scope target /\
                    Sorted.valid_premises scope (U.premise_judgments node.U.premises) /\
                    SC.facts_hold s bc eq other scope rho node.U.premises /\
                    U.check_node_with_membership skolems strict assertions contains node == Some (fact, 0))
          (ensures fact.U.conclusion == node.U.conclusion /\
                   fact.U.hypotheses == U.premise_hypotheses node.U.premises /\
                   SC.fact_holds s bc eq other scope rho fact) =
  if U.check_step node.U.kind node.U.conclusion (U.premise_judgments node.U.premises) then
    U.lemma_mp_check_step node.U.kind node.U.conclusion (U.premise_judgments node.U.premises);
  Sorted.lemma_checked_fact s bc eq other scope rho U.check_step U.checked_theory_lemma
    U.check_binder_with_context skolems strict assertions contains node fact target
