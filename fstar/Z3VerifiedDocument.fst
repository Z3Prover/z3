(*
   Z3VerifiedDocument.fst

   The legacy-route document check in the opt-in accounting mode
   `verified-sorts-v1`: the steps of `Z3ProofDocument.diagnose_document_using`,
   in the same order and with the same rejections, with every node checked by
   `Z3CheckedGuard.check_node_verified`. That check differs from the default
   node check only in the guard that decides a quantifier introduction's
   pending count (`Z3CheckedGuardProof.lemma_check_node_verified`); the
   verdict is the diagnostic's result, from this one pass.

   Each quantifier introduction whose shape the default accepts yields a
   report: its entry index and the guard's outcome (checked, refused,
   exhausted with its phase, or its entries not checked), for additive
   diagnostics. Nothing is shared between documents.
*)
module Z3VerifiedDocument

open Z3AstTheory
open Z3UnifiedProof
open Z3ProofIndex
open Z3ProofDocument
module D = Z3Definitions
module SK = Z3Skolemization
module IT = Z3IdTable
module L = FStar.List.Tot
module G = Z3CheckedGuard
module DD = Z3DagDocument

(* The opt-in mode: `verified-sorts-v1`, or `verified-dag-v1` with the
   prepared certificates of the document's quantifier introductions, by entry. *)
noeq
type accounting =
  | SortsV1
  | DagV1 : companions:index_tree DD.prepared -> accounting

type binder_report = {
  report_index: nat;
  report_entries: nat;
  report_outcome: G.binder_outcome;
  report_graph: option (nat & nat);
}

noeq
type verified_diagnostic = {
  diagnostic: document_diagnostic;
  reports: list binder_report;
}

let entry_count (r:rule) : nat =
  match r with
  | QuantifierIntroduction c -> count_cells 0 c.binder_entries
  | _ -> 0

let verified_entry (acct:accounting) (transform:D.expander) (skolems:list SK.definition) (bound:bool)
                   (defs:list D.definition) (inputs:list judgment) (contains:judgment -> bool)
                   (prev:IT.t checked_fact) (next:nat) (e:entry)
  : option (checked_fact & nat) & option (G.binder_outcome & nat & option (nat & nat)) =
  match prepare_entry_using transform bound defs prev e with
  | None -> None, None
  | Some node ->
    let prepared = match acct with DagV1 cs -> index_get cs next | SortsV1 -> None in
    let r, outcome =
      match acct with
      | SortsV1 -> G.check_node_verified skolems true inputs contains node
      | DagV1 _ -> DD.check_node_dag skolems true inputs contains node prepared in
    let graph = match prepared with Some p -> Some (DD.graph_used p) | None -> None in
    r, (match outcome with Some o -> Some (o, entry_count node.kind, graph) | None -> None)

let rec diagnose_entries_verified (acct:accounting) (transform:D.expander) (skolems:list SK.definition)
                                  (bound:bool) (defs:list D.definition)
                                  (inputs:list judgment) (contains:judgment -> bool)
                                  (cache:IT.t checked_fact) (next pending:nat)
                                  (unmet:list unmet_obligation) (reports:list binder_report)
                                  (entries:list entry)
  : Tot (entries_diagnostic & list binder_report) (decreases entries) =
  match entries with
  | [] -> EntriesChecked cache pending (L.rev unmet), L.rev reports
  | e :: rest ->
    let r, outcome = verified_entry acct transform skolems bound defs inputs contains cache next e in
    let reports = match outcome with
      | Some (o, n, gr) -> { report_index = next; report_entries = n; report_outcome = o; report_graph = gr } :: reports
      | None -> reports in
    match r with
    | None -> EntriesRejected (DocumentRejected ProofEntry (Some next) (Some e.formula)), L.rev reports
    | Some (fact, local) ->
      if local = 0 then
        diagnose_entries_verified acct transform skolems bound defs inputs contains (IT.put cache next fact)
          (next + 1) pending unmet reports rest
      else
        match opt_map_tail (IT.find cache) e.premise_ids with
        | None -> EntriesRejected (DocumentRejected MissingPremise (Some next) (Some e.formula)), L.rev reports
        | Some premises ->
          let obligation = {
            obligation_index = next; obligation_rule = e.rule;
            obligation_conclusion = fact.conclusion;
            obligation_premises = premise_judgments premises;
            obligation_source = e.formula; obligation_count = local;
          } in
          diagnose_entries_verified acct transform skolems bound defs inputs contains (IT.put cache next fact)
            (next + 1) (pending + local) (obligation :: unmet) reports rest

let diagnose_prepared_verified (acct:accounting) (transform:D.expander) (lookup:input_lookup) (doc:document)
                               (bound:bool) (defs:list D.definition)
                               (inputs:list judgment) (skolems:list SK.definition) : verified_diagnostic =
  let entries, reports =
    diagnose_entries_verified acct transform skolems bound defs inputs (lookup inputs) IT.empty 0 0 [] [] doc.entries in
  let diagnostic =
    match entries with
    | EntriesRejected reason ->
      (match reason with
       | DocumentRejected _ _ _ -> reason
       | DocumentChecked _ _ -> DocumentRejected ProofEntry None None)
    | EntriesChecked cache pending unmet ->
      match IT.find cache doc.root with
      | None -> DocumentRejected MissingRoot None None
      | Some node ->
        if not (false_judgment node.conclusion && node.hypotheses = [])
        then DocumentRejected OpenRoot None None
        else if not (D.check_fresh_inputs defs doc.assertions)
        then DocumentRejected DefinitionFreshness None None
        else DocumentChecked pending unmet in
  { diagnostic = diagnostic; reports = reports }

let rejected (stage:diagnostic_stage) : verified_diagnostic =
  { diagnostic = DocumentRejected stage None None; reports = [] }

let diagnose_inputs_verified (acct:accounting) (transform:D.expander) (lookup:input_lookup) (doc:document)
                             (bound:bool) (defs:list D.definition) (expanded:list expr)
                             (inputs:list judgment) : verified_diagnostic =
  match collect_skolems_using transform defs [] doc.entries with
  | None -> rejected SkolemCollection
  | Some choices ->
    match SK.order_context (L.length choices) choices with
    | None -> rejected SkolemCycle
    | Some skolems ->
      if not (SK.fresh_inputs skolems doc.assertions && SK.fresh_inputs skolems expanded)
      then rejected SkolemFreshness
      else diagnose_prepared_verified acct transform lookup doc bound defs inputs skolems

let diagnose_definitions_verified (acct:accounting) (transform:D.expander) (lookup:input_lookup) (doc:document)
                                  (bound:bool) (defs:list D.definition) : verified_diagnostic =
  if not (D.acyclic_using transform (L.length defs) defs defs)
  then rejected DefinitionCycle
  else
    match (if defs = [] then Some doc.assertions
           else D.expand_list_using transform (L.length defs) defs doc.assertions) with
    | None -> rejected DefinitionExpansion
    | Some expanded ->
      match opt_map_tail classify_fact expanded with
      | None -> rejected InputClassification
      | Some inputs -> diagnose_inputs_verified acct transform lookup doc bound defs expanded inputs

let diagnose_document_verified (acct:accounting) (transform:D.expander) (lookup:input_lookup) (doc:document) : verified_diagnostic =
  let bound = not (ground_exprs doc.expressions) in
  if not (logical_decls doc.declarations) then rejected LogicalDeclarations
  else if bound && not (well_formed_exprs doc.expressions) then rejected ExpressionWellFormedness
  else if not (ordinary_facts doc.assertions) then rejected OriginalAssertions
  else if bound && not (scoped_assertions doc.assertions) then rejected AssertionScope
  else
    match document_definitions doc with
    | None -> rejected DefinitionCollection
    | Some defs -> diagnose_definitions_verified acct transform lookup doc bound defs

let diagnose_document_verified_indexed (hash:judgment -> nat) (doc:document) : verified_diagnostic =
  diagnose_document_verified SortsV1 (D.memoized_expander (fun (_, e) -> hash (Holds e))) (document_lookup hash doc) doc

let diagnose_document_dag_indexed (hash:judgment -> nat) (doc:document) (companions:index_tree DD.prepared)
  : verified_diagnostic =
  diagnose_document_verified (DagV1 companions) (D.memoized_expander (fun (_, e) -> hash (Holds e)))
    (document_lookup hash doc) doc

(* --- Additive diagnostic rows ------------------------------------------------------------------- *)

let phase_text (p:Z3CheckedTerms.phase) : string =
  match p with
  | Z3CheckedTerms.Preparation -> "preparation"
  | Z3CheckedTerms.Validation -> "validation"
  | Z3CheckedTerms.Storage -> "storage"

let units_text (name:string) (limit left:nat) : string =
  "\t" ^ name ^ "=" ^ string_of_int (limit - left) ^ "/" ^ string_of_int limit

(* One row per quantifier introduction checked by the opt-in guard: the mode,
   its entry index and binder entries, the outcome, and the units used of each
   budget (`used/limit`), or the exhausted phase. *)
let report_row (dag:bool) (r:binder_report) : string =
  let b = if dag then DD.dag_budget r.report_entries else G.verified_budget r.report_entries in
  let used (left:G.resource_budget) : string =
    units_text "preparation" b.G.preparation left.G.preparation ^
    units_text "validation" b.G.validation left.G.validation ^
    units_text "storage" b.G.storage left.G.storage in
  "resource-accounting\t" ^ (if dag then "verified-dag-v1" else "verified-sorts-v1") ^
  "\tnode=" ^ string_of_int r.report_index ^
  "\tentries=" ^ string_of_int r.report_entries ^ "\toutcome=" ^
  (match r.report_outcome with
   | G.BinderEntriesFailed -> "entries-unchecked"
   | G.BinderGuardChecked left -> "checked" ^ used left
   | G.BinderGuardRefused left -> "refused" ^ used left
   | G.BinderGuardExhausted p -> "exhausted\tphase=" ^ phase_text p
   | G.BinderUnprepared -> "unprepared") ^
  (match r.report_graph with
   | Some (gp, gs) ->
     let shares = r.report_entries + 1 in
     "\tgraph-preparation=" ^ string_of_int gp ^ "/" ^ string_of_int (DD.graph_preparation_per_entry * shares) ^
     "\tgraph-storage=" ^ string_of_int gs ^ "/" ^ string_of_int (DD.graph_storage_per_entry * shares)
   | None -> "")

let rec report_rows_acc (dag:bool) (rs:list binder_report) (acc:list string) : Tot (list string) (decreases rs) =
  match rs with
  | [] -> L.rev acc
  | r :: rest -> report_rows_acc dag rest (report_row dag r :: acc)

let report_rows (rs:list binder_report) : list string = report_rows_acc false rs []

let dag_report_rows (rs:list binder_report) : list string = report_rows_acc true rs []
