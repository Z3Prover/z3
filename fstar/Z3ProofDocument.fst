module Z3ProofDocument

open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
open Z3ObservationalSyntax
open Z3UnifiedProof
open Z3ProofIndex
module D = Z3DefinitionRecognition
module SK = Z3SkolemSyntax
module BF = Z3BvFreshSyntax
module S = Z3ProofSet
module IT = Z3IdTable
module L = FStar.List.Tot
module Replay = Z3DocumentReplay

include Z3DocumentPreparation

let check_entry_with_lookup (skolems:list SK.definition) (strict bound:bool)
                           (defs:list D.definition) (assertions:list judgment) (contains:judgment -> bool)
                           (prev:index_tree checked_fact) (e:entry)
  : option (checked_fact & nat) =
  prepare_entry bound defs prev e >>= check_node_with_membership skolems strict assertions contains

let check_entry_with_context (skolems:list SK.definition)
                            (strict bound:bool) (defs:list D.definition) (assertions:list judgment)
                            (prev:index_tree checked_fact) (e:entry)
  : option (checked_fact & nat) =
  check_entry_with_lookup skolems strict bound defs assertions (linear_lookup assertions) prev e

let check_entry (strict bound:bool) (defs:list D.definition) (assertions:list judgment)
                (prev:index_tree checked_fact) (e:entry)
  : option (checked_fact & nat) =
  check_entry_with_context [] strict bound defs assertions prev e

let rec check_entries_with_lookup (skolems:list SK.definition) (strict bound:bool)
                                 (defs:list D.definition) (assertions:list judgment) (contains:judgment -> bool)
                      (acc:index_tree checked_fact) (next trusted:nat) (entries:list entry)
  : Tot (option (index_tree checked_fact & nat)) (decreases entries) =
  match entries with
  | [] -> Some (acc, trusted)
  | e :: rest ->
    match check_entry_with_lookup skolems strict bound defs assertions contains acc e with
    | None -> None
    | Some (fact, local) ->
      check_entries_with_lookup skolems strict bound defs assertions contains (index_put acc next fact)
        (next + 1) (trusted + local) rest

let check_entries (skolems:list SK.definition) (strict bound:bool) (defs:list D.definition) (assertions:list judgment)
                  (acc:index_tree checked_fact) (next trusted:nat) (entries:list entry)
  : option (index_tree checked_fact & nat) =
  check_entries_with_lookup skolems strict bound defs assertions (linear_lookup assertions) acc next trusted entries

let check_entry_table (skolems:list SK.definition) (strict bound:bool)
                      (defs:list D.definition) (assertions:list judgment) (contains:judgment -> bool)
                      (prev:IT.t checked_fact) (e:entry)
  : option (checked_fact & nat) =
  prepare_entry_table bound defs prev e >>= check_node_with_membership skolems strict assertions contains

let rec check_entries_table (skolems:list SK.definition) (strict bound:bool)
                            (defs:list D.definition) (assertions:list judgment) (contains:judgment -> bool)
                            (acc:IT.t checked_fact) (next trusted:nat) (entries:list entry)
  : Tot (option (IT.t checked_fact & nat)) (decreases entries) =
  match entries with
  | [] -> Some (acc, trusted)
  | e :: rest ->
    match check_entry_table skolems strict bound defs assertions contains acc e with
    | None -> None
    | Some (fact, local) ->
      check_entries_table skolems strict bound defs assertions contains (IT.put acc next fact)
        (next + 1) (trusted + local) rest

let rec lemma_check_entries_table (skolems:list SK.definition) (strict bound:bool)
                                  (defs:list D.definition) (assertions:list judgment) (contains:judgment -> bool)
                                  (acc:IT.t checked_fact) (tree:index_tree checked_fact)
                                  (next trusted:nat) (entries:list entry)
  : Lemma (requires agrees acc tree)
          (ensures entries_agree (check_entries_table skolems strict bound defs assertions contains acc next trusted entries)
                                 (check_entries_with_lookup skolems strict bound defs assertions contains tree next trusted entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    lemma_prepare_entry_table bound defs acc tree e;
    match check_entry_table skolems strict bound defs assertions contains acc e with
    | None -> ()
    | Some (fact, local) ->
      lemma_agrees_put acc tree next fact;
      lemma_check_entries_table skolems strict bound defs assertions contains (IT.put acc next fact)
        (index_put tree next fact) (next + 1) (trusted + local) rest

type entry_checker =
  skolems:list SK.definition -> strict:bool -> bound:bool -> defs:list D.definition ->
  assertions:list judgment -> contains:(judgment -> bool) ->
  prev:IT.t checked_fact -> e:entry ->
  Tot (result:option (checked_fact & nat){
    result == check_entry_table skolems strict bound defs assertions contains prev e})

let checker_using (transform:D.expander) : entry_checker =
  fun skolems strict bound defs assertions contains prev e ->
    lemma_prepare_entry_using transform bound defs prev e;
    prepare_entry_using transform bound defs prev e >>= check_node_with_membership skolems strict assertions contains

let rec check_entries_using (check:entry_checker) (skolems:list SK.definition)
                           (strict bound:bool) (defs:list D.definition)
                           (assertions:list judgment) (contains:judgment -> bool) (acc:IT.t checked_fact)
                           (next trusted:nat) (entries:list entry)
  : Tot (result:option (IT.t checked_fact & nat){
      result == check_entries_table skolems strict bound defs assertions contains acc next trusted entries})
        (decreases entries) =
  match entries with
  | [] -> Some (acc, trusted)
  | e :: rest ->
    match check skolems strict bound defs assertions contains acc e with
    | None -> None
    | Some (fact, local) ->
      check_entries_using check skolems strict bound defs assertions contains (IT.put acc next fact)
        (next + 1) (trusted + local) rest

let lemma_check_entry_lookup (skolems:list SK.definition) (strict bound:bool) (defs:list D.definition)
                             (assertions:list judgment) (contains:judgment -> bool)
                             (prev:index_tree checked_fact) (e:entry)
  : Lemma (requires (forall (query:judgment). contains query == L.mem query assertions))
          (ensures check_entry_with_lookup skolems strict bound defs assertions contains prev e ==
                   check_entry_with_context skolems strict bound defs assertions prev e)
  = match prepare_entry bound defs prev e with
    | None -> ()
    | Some node -> lemma_check_node_membership skolems strict assertions contains node

let rec lemma_check_entries_lookup (skolems:list SK.definition) (strict bound:bool) (defs:list D.definition)
                                   (assertions:list judgment) (contains:judgment -> bool)
                                   (acc:index_tree checked_fact) (next trusted:nat) (entries:list entry)
  : Lemma (requires (forall (query:judgment). contains query == L.mem query assertions))
          (ensures check_entries_with_lookup skolems strict bound defs assertions contains acc next trusted entries ==
                   check_entries skolems strict bound defs assertions acc next trusted entries)
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      lemma_check_entry_lookup skolems strict bound defs assertions contains acc e;
      (match check_entry_with_context skolems strict bound defs assertions acc e with
       | None -> ()
       | Some (fact, local) ->
         lemma_check_entries_lookup skolems strict bound defs assertions contains (index_put acc next fact)
           (next + 1) (trusted + local) rest)

let finish_document (doc:document) (defs:list D.definition) (result:index_tree checked_fact & nat)
  : option nat =
  index_find (fst result) doc.root >>= (fun node ->
  if false_judgment node.conclusion && node.hypotheses = [] &&
     D.check_fresh_inputs defs doc.assertions
  then Some (snd result) else None)

let finish_table (doc:document) (defs:list D.definition) (result:IT.t checked_fact & nat)
  : option nat =
  IT.find (fst result) doc.root >>= (fun node ->
  if false_judgment node.conclusion && node.hypotheses = [] &&
     D.check_fresh_inputs defs doc.assertions
  then Some (snd result) else None)

let lemma_finish_table (doc:document) (defs:list D.definition)
                       (r:option (IT.t checked_fact & nat)) (s:option (index_tree checked_fact & nat))
  : Lemma (requires entries_agree r s)
          (ensures (r >>= finish_table doc defs) == (s >>= finish_document doc defs)) =
  match r, s with
  | Some (tbl, _), Some (tree, _) -> assert (IT.find tbl doc.root == index_find tree doc.root)
  | _, _ -> ()

let check_document_with_lookup (lookup:input_lookup) (doc:document) : option nat =
  prepare_document doc >>= (fun (bound, defs, inputs, skolems) ->
  check_entries_with_lookup skolems true bound defs inputs (lookup inputs) Empty 0 0 doc.entries >>=
  finish_document doc defs)

let check_document (doc:document) : option nat =
  check_document_with_lookup linear_lookup doc

let lemma_check_document_table (lookup:input_lookup) (doc:document)
  : Lemma ((prepare_document doc >>= (fun (bound, defs, inputs, skolems) ->
             check_entries_table skolems true bound defs inputs (lookup inputs) IT.empty 0 0 doc.entries >>=
             finish_table doc defs)) == check_document_with_lookup lookup doc) =
  match prepare_document doc with
  | None -> ()
  | Some (bound, defs, inputs, skolems) ->
    lemma_check_entries_table skolems true bound defs inputs (lookup inputs) IT.empty Empty 0 0 doc.entries;
    lemma_finish_table doc defs
      (check_entries_table skolems true bound defs inputs (lookup inputs) IT.empty 0 0 doc.entries)
      (check_entries_with_lookup skolems true bound defs inputs (lookup inputs) Empty 0 0 doc.entries)

let check_document_using (transform:D.expander) (lookup:input_lookup) (doc:document)
  : result:option nat{result == check_document_with_lookup lookup doc} =
  lemma_prepare_document_using transform doc;
  lemma_check_document_table lookup doc;
  prepare_document_using transform doc >>= (fun (bound, defs, inputs, skolems) ->
  check_entries_using (checker_using transform) skolems true bound defs inputs (lookup inputs)
    IT.empty 0 0 doc.entries >>= finish_table doc defs)

let check_document_indexed (hash:judgment -> nat) (doc:document) : option nat =
  check_document_using (D.memoized_expander (fun (_, e) -> hash (Holds e)))
    (document_lookup hash doc) doc

let lemma_check_document_lookup (lookup:input_lookup) (doc:document)
  : Lemma (check_document_with_lookup lookup doc == check_document doc)
  = match prepare_document doc with
    | None -> ()
    | Some (bound, defs, inputs, skolems) ->
      lemma_check_entries_lookup skolems true bound defs inputs (lookup inputs) Empty 0 0 doc.entries

let lemma_check_document_indexed (hash:judgment -> nat) (doc:document)
  : Lemma (check_document_indexed hash doc == check_document doc)
  = lemma_check_document_lookup (document_lookup hash doc) doc

let diagnose_entries_using (check:entry_checker) (skolems:list SK.definition)
                               (bound:bool) (defs:list D.definition)
                               (inputs:list judgment) (contains:judgment -> bool)
                         (cache:IT.t checked_fact) (next pending:nat)
                         (unmet:list unmet_obligation) (entries:list entry)
  : Tot entries_diagnostic =
  Replay.diagnose_entries_using check skolems bound defs inputs contains cache next pending unmet entries

let diagnose_entries_with_lookup (skolems:list SK.definition)
                         (bound:bool) (defs:list D.definition)
                         (inputs:list judgment) (contains:judgment -> bool)
                         (cache:IT.t checked_fact) (next pending:nat)
                         (unmet:list unmet_obligation) (entries:list entry) : entries_diagnostic =
  diagnose_entries_using (checker_using D.linear_expander) skolems bound defs inputs contains
    cache next pending unmet entries

let diagnose_entries (skolems:list SK.definition) (bound:bool) (defs:list D.definition) (inputs:list judgment)
                     (cache:IT.t checked_fact) (next pending:nat)
                     (unmet:list unmet_obligation) (entries:list entry) : entries_diagnostic =
  diagnose_entries_with_lookup skolems bound defs inputs (linear_lookup inputs) cache next pending unmet entries

let diagnostic_entries_result (d:entries_diagnostic) : option (IT.t checked_fact & nat) =
  match d with EntriesChecked cache pending _ -> Some (cache, pending) | EntriesRejected _ -> None

let lemma_checked_entry_premises (skolems:list SK.definition) (bound:bool)
                                 (defs:list D.definition) (inputs:list judgment)
                                 (contains:judgment -> bool) (cache:IT.t checked_fact) (e:entry)
  : Lemma (requires Some? (check_entry_table skolems true bound defs inputs contains cache e))
          (ensures Some? (opt_map (IT.find cache) e.premise_ids)) =
  match prepare_entry_table bound defs cache e with
  | None -> ()
  | Some _ ->
    (match opt_map (IT.find cache) e.premise_ids with
     | Some _ -> ()
     | None -> ())

let rec lemma_diagnose_entries_using (check:entry_checker) (skolems:list SK.definition)
                                    (bound:bool) (defs:list D.definition)
                                    (inputs:list judgment) (contains:judgment -> bool)
                                    (cache:IT.t checked_fact) (next pending:nat)
                                    (unmet:list unmet_obligation) (entries:list entry)
  : Lemma (diagnostic_entries_result
             (diagnose_entries_using check skolems bound defs inputs contains cache next pending unmet entries) ==
           check_entries_using check skolems true bound defs inputs contains cache next pending entries)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    match check skolems true bound defs inputs contains cache e with
    | None -> ()
    | Some (fact, local) ->
      let cache' = IT.put cache next fact in
      if local = 0 then
        lemma_diagnose_entries_using check skolems bound defs inputs contains cache'
          (next + 1) pending unmet rest
      else (
        lemma_checked_entry_premises skolems bound defs inputs contains cache e;
        match opt_map (IT.find cache) e.premise_ids with
        | None -> ()
        | Some premises ->
          let obligation = {
            obligation_index = next; obligation_rule = e.rule;
            obligation_conclusion = fact.conclusion;
            obligation_premises = premise_judgments premises;
            obligation_source = e.formula; obligation_count = local;
          } in
          lemma_diagnose_entries_using check skolems bound defs inputs contains cache'
            (next + 1) (pending + local) (obligation :: unmet) rest)

let diagnostic_result (d:document_diagnostic) : option nat =
  match d with DocumentChecked n _ -> Some n | DocumentRejected _ _ _ -> None

let diagnose_prepared_document_using (transform:D.expander) (lookup:input_lookup) (doc:document)
                                    (bound:bool) (defs:list D.definition)
                                    (inputs:list judgment) (skolems:list SK.definition) : document_diagnostic =
  match diagnose_entries_using (checker_using transform) skolems bound defs inputs
          (lookup inputs) IT.empty 0 0 [] doc.entries with
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
      else DocumentChecked pending unmet

let lemma_diagnose_prepared_document_using (transform:D.expander) (lookup:input_lookup)
                                           (doc:document) (bound:bool) (defs:list D.definition)
                                           (inputs:list judgment) (skolems:list SK.definition)
  : Lemma (diagnostic_result
             (diagnose_prepared_document_using transform lookup doc bound defs inputs skolems) ==
           (check_entries_using (checker_using transform) skolems true bound defs inputs (lookup inputs)
              IT.empty 0 0 doc.entries >>= finish_table doc defs)) =
  lemma_diagnose_entries_using (checker_using transform) skolems bound defs inputs (lookup inputs)
    IT.empty 0 0 [] doc.entries;
  match diagnose_entries_using (checker_using transform) skolems bound defs inputs
          (lookup inputs) IT.empty 0 0 [] doc.entries with
  | EntriesRejected reason ->
    (match reason with DocumentRejected _ _ _ | DocumentChecked _ _ -> ())
  | EntriesChecked cache _ _ ->
    (match IT.find cache doc.root with None -> () | Some _ -> ())

let diagnose_document_inputs_using (transform:D.expander) (lookup:input_lookup) (doc:document)
                                   (bound:bool) (defs:list D.definition) (expanded:list expr)
                                   (inputs:list judgment) : document_diagnostic =
  match collect_skolems_using transform defs [] doc.entries with
  | None -> DocumentRejected SkolemCollection None None
  | Some choices ->
    match SK.order_context (L.length choices) choices with
    | None -> DocumentRejected SkolemCycle None None
    | Some skolems ->
      if not (SK.fresh_inputs skolems doc.assertions && SK.fresh_inputs skolems expanded)
      then DocumentRejected SkolemFreshness None None
      else diagnose_prepared_document_using transform lookup doc bound defs inputs skolems

let diagnose_document_definitions_using (transform:D.expander) (lookup:input_lookup) (doc:document)
                                        (bound:bool) (defs:list D.definition) : document_diagnostic =
  if not (D.acyclic_using transform (L.length defs) defs defs)
  then DocumentRejected DefinitionCycle None None
  else
    match (if defs = [] then Some doc.assertions
           else D.expand_list_using transform (L.length defs) defs doc.assertions) with
    | None -> DocumentRejected DefinitionExpansion None None
    | Some expanded ->
      match opt_map_tail classify_fact expanded with
      | None -> DocumentRejected InputClassification None None
      | Some inputs -> diagnose_document_inputs_using transform lookup doc bound defs expanded inputs

let diagnose_document_using (transform:D.expander) (lookup:input_lookup) (doc:document) : document_diagnostic =
  let bound = not (ground_exprs doc.expressions) in
  let reject stage = DocumentRejected stage None None in
  if not (logical_decls doc.declarations) then reject LogicalDeclarations
  else if bound && not (well_formed_exprs doc.expressions) then reject ExpressionWellFormedness
  else if not (ordinary_facts doc.assertions) then reject OriginalAssertions
  else if bound && not (scoped_assertions doc.assertions) then reject AssertionScope
  else
    match document_definitions doc with
    | None -> reject DefinitionCollection
    | Some defs -> diagnose_document_definitions_using transform lookup doc bound defs

let diagnose_document_with_lookup (lookup:input_lookup) (doc:document) : document_diagnostic =
  diagnose_document_using D.linear_expander lookup doc

let diagnose_document (doc:document) : document_diagnostic =
  diagnose_document_with_lookup linear_lookup doc

let diagnose_document_indexed (hash:judgment -> nat) (doc:document) : document_diagnostic =
  diagnose_document_using (D.memoized_expander (fun (_, e) -> hash (Holds e)))
    (document_lookup hash doc) doc

let lemma_diagnose_document_inputs_using (transform:D.expander) (lookup:input_lookup)
                                        (doc:document) (bound:bool) (defs:list D.definition)
                                        (expanded:list expr) (inputs:list judgment)
  : Lemma (diagnostic_result
             (diagnose_document_inputs_using transform lookup doc bound defs expanded inputs) ==
           (prepare_skolem_context_using transform defs doc.assertions expanded doc.entries >>=
             (fun skolems ->
               check_entries_using (checker_using transform) skolems true bound defs inputs (lookup inputs)
                 IT.empty 0 0 doc.entries >>= finish_table doc defs))) =
  match collect_skolems_using transform defs [] doc.entries with
  | None -> ()
  | Some choices ->
    match SK.order_context (L.length choices) choices with
    | None -> ()
    | Some skolems ->
      if SK.fresh_inputs skolems doc.assertions && SK.fresh_inputs skolems expanded
      then lemma_diagnose_prepared_document_using transform lookup doc bound defs inputs skolems

let lemma_diagnose_document_definitions_using (transform:D.expander) (lookup:input_lookup)
                                             (doc:document) (bound:bool) (defs:list D.definition)
  : Lemma (diagnostic_result (diagnose_document_definitions_using transform lookup doc bound defs) ==
           (if not (D.acyclic_using transform (L.length defs) defs defs) then None else
            (if defs = [] then Some doc.assertions
             else D.expand_list_using transform (L.length defs) defs doc.assertions) >>= (fun expanded ->
            opt_map_tail classify_fact expanded >>= (fun inputs ->
            prepare_skolem_context_using transform defs doc.assertions expanded doc.entries >>= (fun skolems ->
            check_entries_using (checker_using transform) skolems true bound defs inputs (lookup inputs)
              IT.empty 0 0 doc.entries >>= finish_table doc defs))))) =
  if D.acyclic_using transform (L.length defs) defs defs then (
    match (if defs = [] then Some doc.assertions
           else D.expand_list_using transform (L.length defs) defs doc.assertions) with
    | None -> ()
    | Some expanded ->
      match opt_map_tail classify_fact expanded with
      | None -> ()
      | Some inputs ->
        lemma_diagnose_document_inputs_using transform lookup doc bound defs expanded inputs)

#push-options "--using_facts_from 'Prims FStar.Pervasives Z3ProofIndex Z3Definitions Z3DocumentSyntax Z3DocumentPreparation Z3ProofDocument'"
let lemma_diagnose_document_using (transform:D.expander) (lookup:input_lookup) (doc:document)
  : Lemma (diagnostic_result (diagnose_document_using transform lookup doc) ==
           check_document_using transform lookup doc) =
  let bound = not (ground_exprs doc.expressions) in
  if logical_decls doc.declarations &&
     (not bound || well_formed_exprs doc.expressions) &&
     ordinary_facts doc.assertions &&
     (not bound || scoped_assertions doc.assertions) then (
    match document_definitions doc with
    | None -> ()
    | Some defs -> lemma_diagnose_document_definitions_using transform lookup doc bound defs)
#pop-options

let lemma_diagnose_document_indexed (hash:judgment -> nat) (doc:document)
  : Lemma (diagnostic_result (diagnose_document_indexed hash doc) == check_document_indexed hash doc)
  = lemma_diagnose_document_using (D.memoized_expander (fun (_, e) -> hash (Holds e)))
      (document_lookup hash doc) doc

let check_document_diagnosed_indexed (hash:judgment -> nat) (doc:document)
  : result:(option nat & document_diagnostic){
      fst result == check_document_indexed hash doc /\
      diagnostic_result (snd result) == fst result} =
  let transform = D.memoized_expander (fun (_, e) -> hash (Holds e)) in
  let lookup = document_lookup hash doc in
  lemma_diagnose_document_using transform lookup doc;
  let diagnostic = diagnose_document_using transform lookup doc in
  diagnostic_result diagnostic, diagnostic
