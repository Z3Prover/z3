module Z3SortedRelationalBridge

open Z3AstTheory
module U = Z3UnifiedProof
module Rule = Z3RelationalRuleSyntax
module Sorted = Z3SortedRelational
module D = Z3ExprScope
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module SK = Z3SkolemSyntax

let lemma_default_node (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (skolems:list SK.definition) (strict:bool)
                       (assertions:list U.judgment) (contains:U.judgment -> bool) (node:U.proof_node)
  : Lemma (requires Rule.core_rule node.U.kind /\
                    Sorted.judgments_hold s bc eq other scope rho (U.premise_judgments node.U.premises) /\
                    (match U.relational node.U.conclusion with
                     | Some (_, a, b) -> D.scoped scope a /\ D.scoped scope b
                     | None -> False) /\
                    Some? (U.check_node_with_membership skolems strict assertions contains node))
          (ensures Sorted.judgment_holds s bc eq other scope rho node.U.conclusion) =
  (match U.relational node.U.conclusion with
   | Some (r, a, b) ->
     if U.check_step node.U.kind node.U.conclusion (U.premise_judgments node.U.premises) then
       U.lemma_core_check_step node.U.kind node.U.conclusion
         (U.premise_judgments node.U.premises) r a b
   | None -> ());
  Sorted.lemma_checked_node s bc eq other scope rho U.check_step U.checked_theory_lemma
    U.check_binder_with_context skolems strict assertions contains node

let lemma_default_fact_node (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (scope:list sort) (rho:V.environment base (S.signature s) scope)
                            (skolems:list SK.definition) (strict:bool)
                            (assertions:list U.judgment) (contains:U.judgment -> bool)
                            (node:U.proof_node) (fact:U.checked_fact)
  : Lemma (requires Rule.core_rule node.U.kind /\
                    Sorted.facts_hold s bc eq other scope rho node.U.premises /\
                    (match U.relational node.U.conclusion with
                     | Some (_, a, b) -> D.scoped scope a /\ D.scoped scope b
                     | None -> False) /\
                    U.check_node_with_membership skolems strict assertions contains node == Some (fact, 0))
          (ensures fact.U.conclusion == node.U.conclusion /\
                   fact.U.hypotheses == U.premise_hypotheses node.U.premises /\
                   Sorted.fact_holds s bc eq other scope rho fact) =
  (match U.relational node.U.conclusion with
   | Some (r, a, b) ->
     if U.check_step node.U.kind node.U.conclusion (U.premise_judgments node.U.premises) then
       U.lemma_core_check_step node.U.kind node.U.conclusion
         (U.premise_judgments node.U.premises) r a b
   | None -> ());
  Sorted.lemma_checked_fact_node s bc eq other scope rho U.check_step U.checked_theory_lemma
    U.check_binder_with_context skolems strict assertions contains node fact
