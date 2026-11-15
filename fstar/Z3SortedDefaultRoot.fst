module Z3SortedDefaultRoot

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
module Replay = Z3SortedScopedReplay
module R = Z3ClauseSyntax

let lemma_diagnose_inputs (lookup:P.input_lookup) (doc:P.document)
                          (bound:bool) (defs:list D.definition)
                          (inputs:list U.judgment) (expanded:list expr)
                          (skolems:list SK.definition)
  : Lemma (requires P.prepare_skolem_context defs doc.P.assertions expanded doc.P.entries == Some skolems)
          (ensures P.diagnose_document_inputs_using D.linear_expander lookup doc bound defs expanded inputs ==
                   P.diagnose_prepared_document_using D.linear_expander lookup doc bound defs inputs skolems) =
  match P.collect_skolems_using D.linear_expander defs [] doc.P.entries with
  | None -> ()
  | Some choices ->
    match SK.order_context (FStar.List.Tot.length choices) choices with
    | None -> ()
    | Some _ -> ()

let lemma_prepared_refutation (#base:sort -> Type0) (s:S.checked_schema)
                              (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                              (other:V.interpretation base (S.signature s))
                              (scope:list sort) (rho:V.environment base (S.signature s) scope)
                              (lookup:P.input_lookup) (doc:P.document) (bound:bool)
                              (defs:list D.definition) (inputs:list U.judgment)
                              (skolems:list SK.definition) (obligations:list P.unmet_obligation)
  : Lemma (requires Replay.entries_supported scope bound defs doc.P.entries /\
                    (forall (j:U.judgment).
                      lookup inputs j ==> SC.judgment_holds s bc eq other scope rho j) /\
                    P.diagnose_prepared_document_using D.linear_expander lookup doc bound defs inputs skolems ==
                      P.DocumentChecked 0 obligations)
          (ensures False) =
  let check = P.checker_using D.linear_expander in
  let contains = lookup inputs in
  let good = Replay.scoped_fact s bc eq other scope rho in
  F.lemma_empty good;
  match P.diagnose_entries_using check skolems bound defs inputs contains IT.empty 0 0 [] doc.P.entries with
  | P.EntriesRejected _ -> ()
  | P.EntriesChecked final count unmet ->
    (match IT.find final doc.P.root with
     | None -> ()
     | Some root ->
       Replay.lemma_entries s bc eq other scope rho skolems bound defs inputs contains
         IT.empty 0 [] doc.P.entries final unmet;
       assert (root.U.conclusion == U.Holds R.false_expr /\ root.U.hypotheses == []);
       assert (good root);
       assert (T.truth_at s bc eq other scope rho R.false_expr);
       assert_norm (T.cut_with_boundaries [] 1 R.false_expr == Z3BoundedBoolEquiv.Bool false);
       T.lemma_cut_with_boundaries_at s bc eq other scope rho [] 1 R.false_expr)

let lemma_inputs_refutation (#base:sort -> Type0) (s:S.checked_schema)
                            (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                            (other:V.interpretation base (S.signature s))
                            (scope:list sort) (rho:V.environment base (S.signature s) scope)
                            (lookup:P.input_lookup) (doc:P.document) (bound:bool)
                            (defs:list D.definition) (inputs:list U.judgment) (expanded:list expr)
                            (skolems:list SK.definition) (obligations:list P.unmet_obligation)
  : Lemma (requires P.prepare_skolem_context defs doc.P.assertions expanded doc.P.entries == Some skolems /\
                    Replay.entries_supported scope bound defs doc.P.entries /\
                    (forall (j:U.judgment).
                      lookup inputs j ==> SC.judgment_holds s bc eq other scope rho j) /\
                    P.diagnose_document_inputs_using D.linear_expander lookup doc bound defs expanded inputs ==
                      P.DocumentChecked 0 obligations)
          (ensures False) =
  lemma_diagnose_inputs lookup doc bound defs inputs expanded skolems;
  lemma_prepared_refutation s bc eq other scope rho lookup doc bound defs inputs skolems obligations

