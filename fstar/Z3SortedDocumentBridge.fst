module Z3SortedDocumentBridge

open Z3AstTheory
module U = Z3UnifiedProof
module P = Z3ProofDocument
module D = Z3DefinitionRecognition
module Scope = Z3ExprScope
module IT = Z3IdTable
module SK = Z3SkolemSyntax
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module SC = Z3SortedRelational
module B = Z3SortedRelationalBridge
module F = Z3DocumentFactSemantics
module Rule = Z3RelationalRuleSyntax
module ReplaySem = Z3DocumentReplaySemantics
module L = FStar.List.Tot
module Leaf = Z3SortedLeafFacts
module H = Z3HypothesisSemantics
module SH = Z3SortedHypothesisSemantics
module Lemma = Z3SortedLemmaFacts

let rec lemma_premise_facts (#base:sort -> Type0) (s:S.checked_schema)
                            (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                            (other:V.interpretation base (S.signature s))
                            (scope:list sort) (rho:V.environment base (S.signature s) scope)
                            (facts:list U.checked_fact)
  : Lemma (requires F.facts_hold (SC.fact_holds s bc eq other scope rho) facts)
          (ensures SC.facts_hold s bc eq other scope rho facts)
          (decreases facts) =
  match facts with
  | [] -> ()
  | _ :: rest -> lemma_premise_facts s bc eq other scope rho rest

let lemma_default_entry (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                        (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (skolems:list SK.definition) (strict bound:bool)
                        (defs:list D.definition) (assertions:list U.judgment)
                        (contains:U.judgment -> bool) (table:IT.t U.checked_fact)
                        (entry:P.entry) (node:U.proof_node) (fact:U.checked_fact) (id:nat)
  : Lemma (requires F.table_holds (SC.fact_holds s bc eq other scope rho) table /\
                    P.prepare_entry_table bound defs table entry == Some node /\
                    Rule.core_rule node.U.kind /\
                    (match U.relational node.U.conclusion with
                     | Some (_, a, b) -> Scope.scoped scope a /\ Scope.scoped scope b
                     | None -> False) /\
                    P.check_entry_table skolems strict bound defs assertions contains table entry ==
                      Some (fact, 0))
          (ensures fact.U.conclusion == node.U.conclusion /\
                   fact.U.hypotheses == U.premise_hypotheses node.U.premises /\
                   SC.fact_holds s bc eq other scope rho fact /\
                   F.table_holds (SC.fact_holds s bc eq other scope rho) (IT.put table id fact)) =
  F.lemma_prepared (SC.fact_holds s bc eq other scope rho) D.linear_expander bound defs table entry node;
  lemma_premise_facts s bc eq other scope rho node.U.premises;
  B.lemma_default_fact_node s bc eq other scope rho skolems strict assertions contains node fact;
  F.lemma_put (SC.fact_holds s bc eq other scope rho) table id fact

let supported_entries (scope:list sort) (bound:bool) (defs:list D.definition)
                      (entries:list P.entry) : prop =
  forall (table:IT.t U.checked_fact) (entry:P.entry) (node:U.proof_node).
    L.mem entry entries /\ P.prepare_entry_table bound defs table entry == Some node ==>
    node.U.kind == U.Asserted \/ node.U.kind == U.Hypothesis \/
    (node.U.kind == U.LemmaRule /\
     (match U.proposition node.U.conclusion with
      | Some e -> SH.valid scope e /\ H.valid_list (SH.valid scope) (U.premise_hypotheses node.U.premises)
      | None -> False)) \/
    (Rule.core_rule node.U.kind /\
     (match U.relational node.U.conclusion with
      | Some (_, a, b) -> Scope.scoped scope a /\ Scope.scoped scope b
      | None -> False))

let lemma_default_entries (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (scope:list sort) (rho:V.environment base (S.signature s) scope)
                          (skolems:list SK.definition) (bound:bool) (defs:list D.definition)
                          (assertions:list U.judgment) (contains:U.judgment -> bool)
                          (table:IT.t U.checked_fact) (next:nat)
                          (unmet:list P.unmet_obligation) (entries:list P.entry)
                          (final:IT.t U.checked_fact) (obligations:list P.unmet_obligation)
  : Lemma (requires F.table_holds (SC.fact_holds s bc eq other scope rho) table /\
                    supported_entries scope bound defs entries /\
                    (forall (j:U.judgment). contains j ==> SC.judgment_holds s bc eq other scope rho j) /\
                    P.diagnose_entries_using (P.checker_using D.linear_expander)
                      skolems bound defs assertions contains table next 0 unmet entries ==
                        P.EntriesChecked final 0 obligations)
          (ensures F.table_holds (SC.fact_holds s bc eq other scope rho) final) =
  let good = SC.fact_holds s bc eq other scope rho in
  let check = P.checker_using D.linear_expander in
  let at (cache:IT.t U.checked_fact) (entry:P.entry) (fact:U.checked_fact)
    : Lemma (L.mem entry entries /\ F.table_holds good cache /\
             check skolems true bound defs assertions contains cache entry == Some (fact, 0) ==>
             good fact) =
    let aux (_:squash (L.mem entry entries /\ F.table_holds good cache /\
                       check skolems true bound defs assertions contains cache entry == Some (fact, 0)))
      : Lemma (good fact) =
      match P.prepare_entry_table bound defs cache entry with
      | Some node ->
        if node.U.kind = U.Asserted || node.U.kind = U.Hypothesis then
          Leaf.lemma_checked_leaf s bc eq other scope rho U.check_step U.checked_theory_lemma
            U.check_binder_with_context skolems true assertions contains node fact
        else if node.U.kind = U.LemmaRule then (
          F.lemma_prepared good D.linear_expander bound defs cache entry node;
          lemma_premise_facts s bc eq other scope rho node.U.premises;
          match U.proposition node.U.conclusion with
          | Some concl ->
            Lemma.lemma_checked s bc eq other scope rho U.check_step U.checked_theory_lemma
              U.check_binder_with_context skolems true assertions contains node fact concl
          | None -> ())
        else
          lemma_default_entry s bc eq other scope rho skolems true bound defs assertions contains
            cache entry node fact 0
      | None -> () in
    FStar.Classical.impl_intro aux in
  FStar.Classical.forall_intro_3 at;
  ReplaySem.lemma_checked good check skolems bound defs assertions contains table next unmet entries
    final obligations
