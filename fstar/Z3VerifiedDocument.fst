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
   preparations of the document's quantifier introductions, by entry. *)
noeq
type accounting =
  | SortsV1
  | DagV1 : companions:DD.companions -> accounting

type binder_report = {
  report_index: nat;
  report_entries: nat;
  report_outcome: G.binder_outcome;
  report_graph: option (nat & nat);
  report_unprepared: option DD.unprepared_reason;
  report_debit: option (nat & nat);
  report_forfeit: option (nat & nat);
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

(* The opt-in DAG mode's state through a document's entries: its companions
   and its expansion context (one per document check, with the document's
   definitions `defs`). *)
noeq
type dag_state (defs:list D.definition) =
  | NoDag
  | DagState : cs:DD.companions -> x:DD.context defs (DD.base_graph cs) -> dag_state defs

(* The shares of a document's quantifier introductions, `n + 1` for a
   certificate of `n` entries, by a self tail call. *)
let rec dag_shares (entries:list entry) (acc:nat) : Tot nat (decreases entries) =
  match entries with
  | [] -> acc
  | e :: rest ->
    (match e.rule with
     | QuantifierIntroduction c -> dag_shares rest (acc + count_cells 0 c.binder_entries + 1)
     | _ -> dag_shares rest acc)

(* The document's expansion allowance, set once: the graph's per-share
   allowance for each share of the document's quantifier introductions. *)
let initial_state (acct:accounting) (defs:list D.definition) (entries:list entry) : dag_state defs =
  match acct with
  | SortsV1 -> NoDag
  | DagV1 cs ->
    let shares = dag_shares entries 0 in
    DagState cs (DD.expansion_context defs cs (DD.graph_preparation_per_entry * shares)
                                              (DD.graph_storage_per_entry * shares))

(* The preparation of entry `next` in the opt-in DAG mode: the certificate
   prepared while the document was marshaled, with the document's
   definitions expanded in the document's context (`DD.expand_prepared`), as
   the default expands the certificate it checks (`prepare_entry_using`). *)
let dag_preparation (#defs:list D.definition) (cs:DD.companions) (x:DD.context defs (DD.base_graph cs)) (next:nat)
  : DD.expanded_prep defs (DD.base_graph cs) =
  match DD.preparation_of cs next with
  | DD.Ready p used -> DD.expand_prepared defs x p used
  | DD.Unready w u -> { DD.xprep = DD.Unready w u; DD.xctx = x; DD.xdebit = None; DD.xforfeit = None }

let rec lemma_expanded_using (transform:D.expander) (defs:list D.definition) (es es':list binder_entry)
  : Lemma (requires DD.expanded_rel defs (L.length defs) es es')
          (ensures expand_binder_entries_using transform defs es == Some es')
          (decreases es)
  = match es, es' with
    | _ :: r, _ :: r' -> lemma_expanded_using transform defs r r'
    | _, _ -> ()

(* The certificate the opt-in mode checks is the one the default checks: the
   expansion of the prepared certificate, which the marshaled document holds
   (`Z3NativeProof.marshal_binder`), with the document's definitions. *)
let lemma_dag_preparation (transform:D.expander) (#defs:list D.definition) (cs:DD.companions)
                          (x:DD.context defs (DD.base_graph cs)) (next:nat)
  : Lemma (match DD.preparation_of cs next, (dag_preparation cs x next).DD.xprep with
           | DD.Ready p _, DD.Ready p' _ ->
             expand_rule_using transform defs (QuantifierIntroduction p.DD.pcert) ==
             Some (QuantifierIntroduction p'.DD.pcert)
           | _, _ -> True)
  = match DD.preparation_of cs next, (dag_preparation cs x next).DD.xprep with
    | DD.Ready p _, DD.Ready p' _ ->
      (match defs with
       | [] -> ()
       | _ -> lemma_expanded_using transform defs p.DD.pcert.binder_entries p'.DD.pcert.binder_entries)
    | _, _ -> ()

noeq
type entry_result (defs:list D.definition) = {
  checked: option (checked_fact & nat);
  outcome: option (G.binder_outcome & nat & option (nat & nat) & option DD.unprepared_reason &
                   option (nat & nat) & option (nat & nat));
  state: dag_state defs;
}

let verified_entry (#defs:list D.definition) (transform:D.expander) (skolems:list SK.definition) (bound:bool)
                   (inputs:list judgment) (contains:judgment -> bool)
                   (prev:IT.t checked_fact) (next:nat) (e:entry) (st:dag_state defs)
  : entry_result defs =
  match prepare_entry_using transform bound defs prev e with
  | None -> { checked = None; outcome = None; state = st }
  | Some node ->
    match st with
    | NoDag ->
      let r, o = G.check_node_verified skolems true inputs contains node in
      { checked = r; outcome = (match o with Some o -> Some (o, entry_count node.kind, None, None, None, None) | None -> None);
        state = st }
    | DagState cs x ->
      match node.kind with
      | QuantifierIntroduction _ ->
        let ep = dag_preparation cs x next in
        let prepared = match ep.DD.xprep with DD.Ready p _ -> Some p | _ -> None in
        let r, o = DD.check_node_dag skolems true inputs contains node prepared in
        let graph, why = match ep.DD.xprep with DD.Ready _ u -> Some u, None | DD.Unready w u -> u, Some w in
        { checked = r;
          outcome = (match o with
                     | Some o -> Some (o, entry_count node.kind, graph, why, ep.DD.xdebit, ep.DD.xforfeit)
                     | None -> None);
          state = DagState cs ep.DD.xctx }
      | _ ->
        let r, _ = DD.check_node_dag skolems true inputs contains node None in
        { checked = r; outcome = None; state = st }

let rec diagnose_entries_verified (acct:accounting) (transform:D.expander) (skolems:list SK.definition)
                                  (bound:bool) (defs:list D.definition)
                                  (inputs:list judgment) (contains:judgment -> bool)
                                  (cache:IT.t checked_fact) (next pending:nat)
                                  (unmet:list unmet_obligation) (reports:list binder_report)
                                  (st:dag_state defs) (entries:list entry)
  : Tot (entries_diagnostic & list binder_report) (decreases entries) =
  match entries with
  | [] -> EntriesChecked cache pending (L.rev unmet), L.rev reports
  | e :: rest ->
    let er = verified_entry transform skolems bound inputs contains cache next e st in
    let reports = match er.outcome with
      | Some (o, n, gr, why, xd, xf) ->
        { report_index = next; report_entries = n; report_outcome = o; report_graph = gr; report_unprepared = why;
          report_debit = xd; report_forfeit = xf }
        :: reports
      | None -> reports in
    match er.checked with
    | None -> EntriesRejected (DocumentRejected ProofEntry (Some next) (Some e.formula)), L.rev reports
    | Some (fact, local) ->
      if local = 0 then
        diagnose_entries_verified acct transform skolems bound defs inputs contains (IT.put cache next fact)
          (next + 1) pending unmet reports er.state rest
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
            (next + 1) (pending + local) (obligation :: unmet) reports er.state rest

let diagnose_prepared_verified (acct:accounting) (transform:D.expander) (lookup:input_lookup) (doc:document)
                               (bound:bool) (defs:list D.definition)
                               (inputs:list judgment) (skolems:list SK.definition) : verified_diagnostic =
  let entries, reports =
    diagnose_entries_verified acct transform skolems bound defs inputs (lookup inputs) IT.empty 0 0 [] []
      (initial_state acct defs doc.entries) doc.entries in
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

let diagnose_document_dag_indexed (hash:judgment -> nat) (doc:document) (companions:DD.companions)
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

let invalid_text (w:DD.invalid_reason) : string =
  match w with
  | DD.MissingExpression -> "missing-expression"
  | DD.MissingSort -> "missing-sort"
  | DD.MissingDeclaration -> "missing-declaration"
  | DD.RefusedNode -> "refused-node"

(* Why a quantifier introduction has no prepared certificate: a phase of the
   checked graph's budget exhausted (`graph-preparation`, `graph-storage`), an
   input the graph's builders do not take, a clausal document, the expansion
   of the document's definitions on the graph stopped (a phase exhausted, or
   a node it does not rebuild), or no preparation recorded. *)
let unprepared_text (why:DD.unprepared_reason) : string =
  match why with
  | DD.UnpreparedExhausted p -> "exhausted\tphase=graph-" ^ phase_text p
  | DD.UnpreparedInvalid w -> "invalid:" ^ invalid_text w
  | DD.UnpreparedClausal -> "clausal"
  | DD.UnpreparedExpansionExhausted p -> "expansion-exhausted\tphase=graph-" ^ phase_text p
  | DD.UnpreparedExpansionInvalid -> "expansion-invalid"
  | DD.UnpreparedAbsent -> "absent"

(* One row per quantifier introduction checked by the opt-in guard: the mode,
   its entry index and binder entries, the outcome, and the units used of each
   budget (`used/limit`), or the exhausted phase; for a certificate without a
   prepared form, why (`reason=`). The graph's units are those its steps used
   of the certificate's allowance, for an unprepared one those of the steps
   before the one that stopped. A certificate of a document with definitions
   adds the debit of its expansion to the document's one expansion
   allowance (`expansion-debit-*`), or, when its expansion stopped, what that
   allowance held, forfeited (`expansion-forfeited-*`). *)
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
   | G.BinderUnprepared ->
     "unprepared" ^ (match r.report_unprepared with Some why -> "\treason=" ^ unprepared_text why | None -> "")) ^
  (match r.report_graph with
   | Some (gp, gs) ->
     let shares = r.report_entries + 1 in
     "\tgraph-preparation=" ^ string_of_int gp ^ "/" ^ string_of_int (DD.graph_preparation_per_entry * shares) ^
     "\tgraph-storage=" ^ string_of_int gs ^ "/" ^ string_of_int (DD.graph_storage_per_entry * shares)
   | None -> "") ^
  (match r.report_debit with
   | Some (ep, es) -> "\texpansion-debit-preparation=" ^ string_of_int ep ^ "\texpansion-debit-storage=" ^ string_of_int es
   | None -> "") ^
  (match r.report_forfeit with
   | Some (ep, es) ->
     "\texpansion-forfeited-preparation=" ^ string_of_int ep ^ "\texpansion-forfeited-storage=" ^ string_of_int es
   | None -> "")

let rec report_rows_acc (dag:bool) (rs:list binder_report) (acc:list string) : Tot (list string) (decreases rs) =
  match rs with
  | [] -> L.rev acc
  | r :: rest -> report_rows_acc dag rest (report_row dag r :: acc)

let report_rows (rs:list binder_report) : list string = report_rows_acc false rs []

let dag_report_rows (rs:list binder_report) : list string = report_rows_acc true rs []
