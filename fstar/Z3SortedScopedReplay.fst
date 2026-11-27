module Z3SortedScopedReplay

open Z3AstTheory
module U = Z3UnifiedProof
module P = Z3ProofDocument
module D = Z3DefinitionRecognition
module IT = Z3IdTable
module SK = Z3SkolemSyntax
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module SC = Z3SortedRelational
module F = Z3DocumentFactSemantics
module ReplaySem = Z3DocumentReplaySemantics
module Bridge = Z3SortedRelationalBridge
module Leaf = Z3SortedLeafFacts
module Lemma = Z3SortedLemmaFacts
module Rule = Z3RelationalRuleSyntax
module H = Z3HypothesisSemantics
module SH = Z3SortedHypothesisSemantics
module Scope = Z3ExprScope
module L = FStar.List.Tot
module MP = Z3SortedModusPonens
module MPBridge = Z3SortedModusPonensBridge

let scoped_fact (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (scope:list sort) (rho:V.environment base (S.signature s) scope)
                (fact:U.checked_fact) : prop =
  SC.fact_holds s bc eq other scope rho fact /\
  MP.valid_judgment scope fact.U.conclusion /\
  H.valid_list (SH.valid scope) fact.U.hypotheses

let rec lemma_premises (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (facts:list U.checked_fact)
  : Lemma (requires F.facts_hold (scoped_fact s bc eq other scope rho) facts)
          (ensures SC.facts_hold s bc eq other scope rho facts /\
                   H.valid_list (SH.valid scope) (U.premise_hypotheses facts) /\
                   MP.valid_premises scope (U.premise_judgments facts))
          (decreases facts) =
  match facts with
  | [] -> ()
  | fact :: rest ->
    lemma_premises s bc eq other scope rho rest;
    H.lemma_valid_union (SH.valid scope) fact.U.hypotheses (U.premise_hypotheses rest)

let node_supported (scope:list sort) (node:U.proof_node) : prop =
  ((node.U.kind == U.Asserted \/ node.U.kind == U.Hypothesis \/ node.U.kind == U.LemmaRule \/
    node.U.kind == U.ModusPonens \/ node.U.kind == U.ObservationalMP) /\
   (match U.proposition node.U.conclusion with
    | Some e -> SH.valid scope e
    | None -> False)) \/
  (Rule.core_rule node.U.kind /\
   (match U.relational node.U.conclusion with
    | Some (_, a, b) -> Scope.scoped scope a /\ Scope.scoped scope b
    | None -> False))

let entries_supported (scope:list sort) (bound:bool) (defs:list D.definition)
                      (entries:list P.entry) : prop =
  forall (table:IT.t U.checked_fact) (entry:P.entry) (node:U.proof_node).
    L.mem entry entries /\ P.prepare_entry_table bound defs table entry == Some node ==>
    node_supported scope node

let lemma_core_valid (scope:list sort) (j:U.judgment)
  : Lemma (requires U.well_formed j /\
                    (match U.relational j with
                     | Some (_, a, b) -> Scope.scoped scope a /\ Scope.scoped scope b
                     | None -> False))
          (ensures MP.valid_judgment scope j) =
  match j with
  | U.Equal a b ->
    assert (get_sort a == get_sort b);
    V.lemma_sort_eq (get_sort a) (get_sort a);
    V.lemma_sort_eq (get_sort b) (get_sort a);
    assert (sorts_match [a; b] [get_sort a; get_sort a]);
    assert (Scope.scoped_args scope [a; b]);
    assert (Scope.scoped scope (Z3ClauseSyntax.mk_eq_expr a b));
    assert (SH.valid scope (Z3ClauseSyntax.mk_eq_expr a b))
  | U.Observational _ _ -> ()
  | U.Holds _ -> ()

let lemma_entry (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (scope:list sort) (rho:V.environment base (S.signature s) scope)
                (skolems:list SK.definition) (bound:bool) (defs:list D.definition)
                (assertions:list U.judgment) (contains:U.judgment -> bool)
                (table:IT.t U.checked_fact) (entry:P.entry) (node:U.proof_node) (fact:U.checked_fact)
  : Lemma (requires F.table_holds (scoped_fact s bc eq other scope rho) table /\
                    P.prepare_entry_table bound defs table entry == Some node /\
                    node_supported scope node /\
                    (contains node.U.conclusion ==> SC.judgment_holds s bc eq other scope rho node.U.conclusion) /\
                    P.check_entry_table skolems true bound defs assertions contains table entry == Some (fact, 0))
          (ensures scoped_fact s bc eq other scope rho fact) =
  F.lemma_prepared (scoped_fact s bc eq other scope rho) D.linear_expander bound defs table entry node;
  lemma_premises s bc eq other scope rho node.U.premises;
  if node.U.kind = U.Asserted || node.U.kind = U.Hypothesis then
    Leaf.lemma_checked_leaf s bc eq other scope rho U.check_step U.checked_theory_lemma
      U.check_binder_with_context skolems true assertions contains node fact
  else if node.U.kind = U.LemmaRule then (
    match U.proposition node.U.conclusion with
    | Some concl ->
      Lemma.lemma_checked s bc eq other scope rho U.check_step U.checked_theory_lemma
        U.check_binder_with_context skolems true assertions contains node fact concl;
      H.lemma_valid_remaining (SH.valid scope) (U.premise_hypotheses node.U.premises) concl
    | None -> ())
  else if node.U.kind = U.ModusPonens || node.U.kind = U.ObservationalMP then (
    match U.proposition node.U.conclusion with
    | Some concl ->
      MPBridge.lemma_default_fact s bc eq other scope rho skolems true assertions contains node fact concl
    | None -> ())
  else
    (lemma_core_valid scope node.U.conclusion;
     Bridge.lemma_default_fact_node s bc eq other scope rho skolems true assertions contains node fact)

let lemma_entries (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                  (scope:list sort) (rho:V.environment base (S.signature s) scope)
                  (skolems:list SK.definition) (bound:bool) (defs:list D.definition)
                  (assertions:list U.judgment) (contains:U.judgment -> bool)
                  (table:IT.t U.checked_fact) (next:nat)
                  (unmet:list P.unmet_obligation) (entries:list P.entry)
                  (final:IT.t U.checked_fact) (obligations:list P.unmet_obligation)
  : Lemma (requires F.table_holds (scoped_fact s bc eq other scope rho) table /\
                    entries_supported scope bound defs entries /\
                    (forall (j:U.judgment). contains j ==> SC.judgment_holds s bc eq other scope rho j) /\
                    P.diagnose_entries_using (P.checker_using D.linear_expander)
                      skolems bound defs assertions contains table next 0 unmet entries ==
                        P.EntriesChecked final 0 obligations)
          (ensures F.table_holds (scoped_fact s bc eq other scope rho) final) =
  let good = scoped_fact s bc eq other scope rho in
  let check = P.checker_using D.linear_expander in
  let at (cache:IT.t U.checked_fact) (entry:P.entry) (fact:U.checked_fact)
    : Lemma (L.mem entry entries /\ F.table_holds good cache /\
             check skolems true bound defs assertions contains cache entry == Some (fact, 0) ==>
             good fact) =
    let aux (_:squash (L.mem entry entries /\ F.table_holds good cache /\
                       check skolems true bound defs assertions contains cache entry == Some (fact, 0)))
      : Lemma (good fact) =
      match P.prepare_entry_table bound defs cache entry with
      | Some node -> lemma_entry s bc eq other scope rho skolems bound defs assertions contains cache entry node fact
      | None -> () in
    FStar.Classical.impl_intro aux in
  FStar.Classical.forall_intro_3 at;
  ReplaySem.lemma_checked good check skolems bound defs assertions contains table next unmet entries
    final obligations
