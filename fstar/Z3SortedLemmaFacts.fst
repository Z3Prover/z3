module Z3SortedLemmaFacts

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module Node = Z3UnifiedNode
module SK = Z3SkolemSyntax
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module SC = Z3SortedRelational
module CS = Z3ClausalSemantics
module H = Z3HypothesisSemantics
module SH = Z3SortedHypothesisSemantics
module R = Z3ClauseSyntax

let lemma_proposition (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (scope:list sort) (rho:V.environment base (S.signature s) scope)
                      (j:U.judgment) (e:expr)
  : Lemma (requires U.well_formed j /\ U.proposition j == Some e /\ SH.valid scope e /\
                    T.truth_at s bc eq other scope rho e)
          (ensures SC.judgment_holds s bc eq other scope rho j) =
  match j with
  | U.Equal a b -> T.lemma_equality_at s bc eq other scope rho a b
  | _ -> ()

let lemma_checked (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (scope:list sort) (rho:V.environment base (S.signature s) scope)
                  (check_step:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                  (check_theory:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                  (check_binder:list SK.definition -> list U.judgment -> U.binder_certificate ->
                                U.judgment -> Tot bool)
                  (skolems:list SK.definition) (strict:bool)
                  (assertions:list U.judgment) (contains:U.judgment -> bool)
                  (node:U.proof_node) (fact:U.checked_fact) (concl:expr)
  : Lemma (requires node.U.kind == U.LemmaRule /\
                    U.proposition node.U.conclusion == Some concl /\ SH.valid scope concl /\
                    H.valid_list (SH.valid scope) (U.premise_hypotheses node.U.premises) /\
                    SC.facts_hold s bc eq other scope rho node.U.premises /\
                    Node.check_node_with_membership check_step check_theory check_binder
                      skolems strict assertions contains node == Some (fact, 0))
          (ensures fact.U.conclusion == node.U.conclusion /\
                   SC.fact_holds s bc eq other scope rho fact) =
  if CS.conj_holds (T.truth_at s bc eq other scope rho) fact.U.hypotheses then (
    if T.truth_at s bc eq other scope rho concl then
      lemma_proposition s bc eq other scope rho node.U.conclusion concl
    else (
      SH.lemma_model s bc eq other scope rho;
      SH.lemma_valid_clause scope concl;
      H.lemma_remaining (T.truth_at s bc eq other scope rho) (SH.valid scope)
        (U.premise_hypotheses node.U.premises) concl;
      H.lemma_premises (T.truth_at s bc eq other scope rho)
        (SC.judgment_holds s bc eq other scope rho) node.U.premises;
      T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 R.false_expr))
