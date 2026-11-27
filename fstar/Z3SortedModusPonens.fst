module Z3SortedModusPonens

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module MP = Z3ModusPonensSyntax
module R = Z3ClauseSyntax
module Ops = Z3CanonicalOps
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module SC = Z3SortedRelational
module SH = Z3SortedHypothesisSemantics
module D = Z3ExprScope
module H = Z3HypothesisSemantics
module CS = Z3ClausalSemantics
module Node = Z3UnifiedNode
module SK = Z3SkolemSyntax

let valid_judgment (scope:list sort) (j:U.judgment) : bool =
  match j with
  | U.Observational a b -> D.scoped scope a && D.scoped scope b
  | _ -> (match U.proposition j with Some e -> SH.valid scope e | None -> false)

let rec valid_premises (scope:list sort) (js:list U.judgment) : Tot bool (decreases js) =
  match js with
  | [] -> true
  | j :: rest -> valid_judgment scope j && valid_premises scope rest

let lemma_proposition (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                      (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                      (scope:list sort) (rho:V.environment base (S.signature s) scope)
                      (j:U.judgment) (e:expr)
  : Lemma (requires U.well_formed j /\ U.proposition j == Some e /\ SH.valid scope e)
          (ensures SC.judgment_holds s bc eq other scope rho j <==>
                   T.truth_at s bc eq other scope rho e) =
  match j with
  | U.Equal a b -> T.lemma_equality_at s bc eq other scope rho a b
  | _ -> ()

let lemma_checked (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (scope:list sort) (rho:V.environment base (S.signature s) scope)
                  (kind:U.rule) (concl:U.judgment) (js:list U.judgment) (target:expr)
  : Lemma (requires U.well_formed concl /\ U.judgments_wf js /\
                    U.proposition concl == Some target /\ SH.valid scope target /\
                    valid_premises scope js /\ SC.judgments_hold s bc eq other scope rho js /\
                    MP.step kind concl js)
          (ensures SC.judgment_holds s bc eq other scope rho concl) =
  (match kind, js with
   | U.ObservationalMP, [j; U.Observational a b] ->
     lemma_proposition s bc eq other scope rho j a;
     T.lemma_observations_values_at s bc eq other scope rho a b;
     assert (T.truth_at s bc eq other scope rho target)
   | U.ModusPonens, [j; k] ->
     (match U.proposition j, U.proposition k with
      | Some a, Some (App f [p; q]) ->
        lemma_proposition s bc eq other scope rho j a;
        lemma_proposition s bc eq other scope rho k (App f [p; q]);
        if Ops.canonical_eq f then
          T.lemma_boolean_equality_at s bc eq other scope rho p q
        else
          T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 (App f [p; q]);
        assert (T.truth_at s bc eq other scope rho target)
      | _, _ -> ())
   | _, _ -> ());
  lemma_proposition s bc eq other scope rho concl target

let lemma_checked_fact (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (check_step:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                       (check_theory:U.rule -> U.judgment -> list U.judgment -> Tot bool)
                       (check_binder:list SK.definition -> list U.judgment -> U.binder_certificate ->
                                     U.judgment -> Tot bool)
                       (skolems:list SK.definition) (strict:bool)
                       (assertions:list U.judgment) (contains:U.judgment -> bool)
                       (node:U.proof_node) (fact:U.checked_fact) (target:expr)
  : Lemma (requires (node.U.kind == U.ModusPonens \/ node.U.kind == U.ObservationalMP) /\
                    U.proposition node.U.conclusion == Some target /\ SH.valid scope target /\
                    valid_premises scope (U.premise_judgments node.U.premises) /\
                    SC.facts_hold s bc eq other scope rho node.U.premises /\
                    (check_step node.U.kind node.U.conclusion (U.premise_judgments node.U.premises) ==>
                     MP.step node.U.kind node.U.conclusion (U.premise_judgments node.U.premises)) /\
                    Node.check_node_with_membership check_step check_theory check_binder
                      skolems strict assertions contains node == Some (fact, 0))
          (ensures fact.U.conclusion == node.U.conclusion /\
                   fact.U.hypotheses == U.premise_hypotheses node.U.premises /\
                   SC.fact_holds s bc eq other scope rho fact) =
  if CS.conj_holds (T.truth_at s bc eq other scope rho) fact.U.hypotheses then (
    H.lemma_premises (T.truth_at s bc eq other scope rho)
      (SC.judgment_holds s bc eq other scope rho) node.U.premises;
    lemma_checked s bc eq other scope rho node.U.kind node.U.conclusion
      (U.premise_judgments node.U.premises) target)
