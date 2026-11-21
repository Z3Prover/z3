module Z3SortedDocumentBridgeTests

open Z3AstTheory
module U = Z3UnifiedProof
module P = Z3ProofDocument
module I = Z3ProofIndex
module IT = Z3IdTable
module O = Z3ObservationalSyntax
module F = Z3DocumentFactSemantics
module B = Z3SortedDocumentBridge
module Cases = Z3SortedRelationalTests
module SC = Z3SortedRelational
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Scope = Z3ExprScope
module Rule = Z3RelationalRuleSyntax
module L = FStar.List.Tot
module H = Z3HypothesisSemantics
module SH = Z3SortedHypothesisSemantics

let first : U.checked_fact = {
  U.conclusion = U.Observational Cases.p Cases.q;
  U.hypotheses = [Cases.p; Cases.q];
}

let second : U.checked_fact = {
  U.conclusion = U.Observational Cases.q Cases.z;
  U.hypotheses = [Cases.q; Cases.z];
}

let table = IT.put (IT.put IT.empty 0 first) 1 second
let entry : P.entry = {
  P.rule = U.Transitivity;
  P.formula = O.mk_oeq_expr Cases.p Cases.z;
  P.premise_ids = [0; 1];
}

let default_entry (#base:sort -> Type0) (s:S.checked_schema)
                  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                  (other:V.interpretation base (S.signature s))
                  (rho:V.environment base (S.signature s) Cases.scope)
  : Lemma (requires SC.fact_holds s bc eq other Cases.scope rho first /\
                    SC.fact_holds s bc eq other Cases.scope rho second)
          (ensures SC.fact_holds s bc eq other Cases.scope rho Cases.conditional_fact /\
                   F.table_holds (SC.fact_holds s bc eq other Cases.scope rho)
                     (IT.put table 2 Cases.conditional_fact)) =
  let good = SC.fact_holds s bc eq other Cases.scope rho in
  F.lemma_empty good;
  F.lemma_put good IT.empty 0 first;
  F.lemma_put good (IT.put IT.empty 0 first) 1 second;
  IT.lemma_find_put (IT.put IT.empty 0 first) 1 second 0;
  IT.lemma_find_put (IT.put IT.empty 0 first) 1 second 1;
  IT.lemma_find_put IT.empty 0 first 0;
  I.lemma_opt_map_tail (IT.find table) [0; 1];
  assert (P.prepare_entry_table false [] table entry == Some Cases.conditional_node);
  assert (P.check_entry_table [] false false [] [] (fun _ -> false) table entry ==
          Some (Cases.conditional_fact, 0));
  B.lemma_default_entry s bc eq other Cases.scope rho [] false false [] [] (fun _ -> false)
    table entry Cases.conditional_node Cases.conditional_fact 2

let missing_entry : P.entry = { entry with P.premise_ids = [0; 2] }

let missing_premise ()
  : Lemma (P.prepare_entry_table false [] table missing_entry == None) =
  IT.lemma_find_empty #U.checked_fact 2;
  IT.lemma_find_put IT.empty 0 first 2;
  IT.lemma_find_put (IT.put IT.empty 0 first) 1 second 2;
  I.lemma_opt_map_tail (IT.find table) [0; 2]

let core_entry ()
  : Lemma (B.supported_entries Cases.scope false [] [entry]) =
  let at (cache:IT.t U.checked_fact) (e:P.entry) (node:U.proof_node)
    : Lemma (L.mem e [entry] /\ P.prepare_entry_table false [] cache e == Some node ==>
             Rule.core_rule node.U.kind /\
             (match U.relational node.U.conclusion with
              | Some (_, a, b) -> Scope.scoped Cases.scope a /\ Scope.scoped Cases.scope b
              | None -> False)) =
    I.lemma_opt_map_tail (IT.find cache) entry.P.premise_ids;
    match I.opt_map (IT.find cache) entry.P.premise_ids with
    | Some _ -> ()
    | None -> () in
  FStar.Classical.forall_intro_3 at

let default_replay (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (rho:V.environment base (S.signature s) Cases.scope)
  : Lemma (requires SC.fact_holds s bc eq other Cases.scope rho first /\
                    SC.fact_holds s bc eq other Cases.scope rho second)
          (ensures F.table_holds (SC.fact_holds s bc eq other Cases.scope rho)
                     (IT.put table 2 Cases.conditional_fact)) =
  let good = SC.fact_holds s bc eq other Cases.scope rho in
  F.lemma_empty good;
  F.lemma_put good IT.empty 0 first;
  F.lemma_put good (IT.put IT.empty 0 first) 1 second;
  IT.lemma_find_put (IT.put IT.empty 0 first) 1 second 0;
  IT.lemma_find_put (IT.put IT.empty 0 first) 1 second 1;
  IT.lemma_find_put IT.empty 0 first 0;
  I.lemma_opt_map_tail (IT.find table) [0; 1];
  core_entry ();
  assert (P.prepare_entry_table false [] table entry == Some Cases.conditional_node);
  assert_norm (U.check_node_with_membership [] true [] (fun _ -> false) Cases.conditional_node ==
               Some (Cases.conditional_fact, 0));
  assert (P.check_entry_table [] true false [] [] (fun _ -> false) table entry ==
          Some (Cases.conditional_fact, 0));
  assert (P.checker_using Z3DefinitionRecognition.linear_expander
            [] true false [] [] (fun _ -> false) table entry ==
          Some (Cases.conditional_fact, 0));
  assert (P.diagnose_entries_using (P.checker_using Z3DefinitionRecognition.linear_expander)
            [] false [] [] (fun _ -> false) table 2 0 [] [entry] ==
          P.EntriesChecked (IT.put table 2 Cases.conditional_fact) 0 []);
  B.lemma_default_entries s bc eq other Cases.scope rho [] false [] [] (fun _ -> false)
    table 2 [] [entry] (IT.put table 2 Cases.conditional_fact) []

let leaf_entry : P.entry = { P.rule = U.Hypothesis; P.formula = Cases.p; P.premise_ids = [] }
let leaf_fact : U.checked_fact = { U.conclusion = U.Holds Cases.p; U.hypotheses = [Cases.p] }

let leaf_supported ()
  : Lemma (B.supported_entries [] false [] [leaf_entry]) =
  let at (cache:IT.t U.checked_fact) (e:P.entry) (node:U.proof_node)
    : Lemma (L.mem e [leaf_entry] /\ P.prepare_entry_table false [] cache e == Some node ==>
             node.U.kind == U.Asserted \/ node.U.kind == U.Hypothesis \/
             (node.U.kind == U.LemmaRule /\
              (match U.proposition node.U.conclusion with
               | Some concl -> SH.valid [] concl /\ H.valid_list (SH.valid []) (U.premise_hypotheses node.U.premises)
               | None -> False)) \/
             (Rule.core_rule node.U.kind /\
              (match U.relational node.U.conclusion with
               | Some (_, a, b) -> Scope.scoped [] a /\ Scope.scoped [] b
               | None -> False))) = () in
  FStar.Classical.forall_intro_3 at

let unscoped_leaf_replay (#base:sort -> Type0) (s:S.checked_schema)
                         (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                         (other:V.interpretation base (S.signature s))
                         (rho:V.environment base (S.signature s) [])
  : Lemma (F.table_holds (SC.fact_holds s bc eq other [] rho) (IT.put IT.empty 0 leaf_fact)) =
  F.lemma_empty (SC.fact_holds s bc eq other [] rho);
  leaf_supported ();
  assert_norm (P.diagnose_entries_using (P.checker_using Z3DefinitionRecognition.linear_expander)
                 [] false [] [] (fun _ -> false) IT.empty 0 0 [] [leaf_entry] ==
               P.EntriesChecked (IT.put IT.empty 0 leaf_fact) 0 []);
  B.lemma_default_entries s bc eq other [] rho [] false [] [] (fun _ -> false)
    IT.empty 0 [] [leaf_entry] (IT.put IT.empty 0 leaf_fact) []
