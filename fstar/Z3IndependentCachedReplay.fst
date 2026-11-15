module Z3IndependentCachedReplay

open Z3AstTheory
module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module Prep = Z3DocumentPreparation
module U = Z3UnifiedProofSyntax
module SP = Z3SortedProof
module Congruence = Z3IndependentCongruence
module IT = Z3IdTable
module I = Z3ProofIndex
module L = FStar.List.Tot

let evaluate_entry (s:S.checked_schema) (assertions:list expr)
                   (input:P.entry & option (list U.checked_fact))
  : option (U.proof_node & U.checked_fact & nat) =
  let entry, premises = input in
  match SP.prepare_entry_from s premises entry with
  | None -> None
  | Some node ->
    match Congruence.check_node s assertions node with
    | None -> None
    | Some (fact, local) -> Some (node, fact, local)

let cached_item (s:S.checked_schema) (assertions:list expr) =
  item:((P.entry & option (list U.checked_fact)) &
        option (U.proof_node & U.checked_fact & nat)){
    snd item == evaluate_entry s assertions (fst item)}

noeq type cache (s:S.checked_schema) (assertions:list expr) = {
  known: IT.t (cached_item s assertions);
  recent: list (nat & cached_item s assertions);
}

let empty (s:S.checked_schema) (assertions:list expr) : cache s assertions =
  { known = IT.empty; recent = [] }

let seal (s:S.checked_schema) (assertions:list expr) (memo:cache s assertions)
  : cache s assertions =
  let known = L.fold_left (fun known item -> IT.put known (fst item) (snd item))
                         memo.known (L.rev memo.recent) in
  { known = known; recent = [] }

let check_entry (s:S.checked_schema) (assertions:list expr)
                (memo:cache s assertions) (index:nat) (entry:P.entry)
                (premises:option (list U.checked_fact)) =
  let input = entry, premises in
  let found =
    match IT.find memo.known index with
    | Some (previous, result) -> if previous = input then Some result else None
    | None -> None in
  match found with
  | Some result -> result, memo
  | None ->
    let result = evaluate_entry s assertions input in
    result, { memo with recent = (index, (input, result)) :: memo.recent }

let rec diagnose_entries (s:S.checked_schema) (assertions:list expr)
                         (memo:cache s assertions) (facts:IT.t U.checked_fact)
                         (next pending:nat) (unmet:list P.unmet_obligation)
                         (entries:list P.entry)
  : Tot (result:(Prep.entries_diagnostic & cache s assertions){
      fst result == SP.diagnose_entries s assertions facts next pending unmet entries})
        (decreases entries) =
  match entries with
  | [] -> Prep.EntriesChecked facts pending (L.rev unmet), memo
  | e :: rest ->
    let reject = Prep.EntriesRejected (P.DocumentRejected P.ProofEntry (Some next) (Some e.P.formula)) in
    let premises = I.opt_map_tail (IT.find facts) e.P.premise_ids in
    let checked, memo = check_entry s assertions memo next e premises in
    match checked with
    | None -> reject, memo
    | Some (node, fact, local) ->
        let facts = IT.put facts next fact in
        let unmet =
          if local = 0 then unmet
          else {
            P.obligation_index = next; obligation_rule = e.P.rule;
            obligation_conclusion = fact.U.conclusion;
            obligation_premises = U.premise_judgments node.U.premises;
            obligation_source = e.P.formula; obligation_count = local;
          } :: unmet in
        diagnose_entries s assertions memo facts (next + 1) (pending + local) unmet rest

let diagnose_document (s:S.checked_schema) (doc:P.document)
                      (memo:cache s doc.P.assertions) =
  if not (S.valid s) then P.DocumentRejected P.LogicalDeclarations None None, memo
  else if not (SP.boolean_expressions s doc.P.assertions && U.ordinary_facts doc.P.assertions)
  then P.DocumentRejected P.OriginalAssertions None None, memo
  else
    let result, memo = diagnose_entries s doc.P.assertions memo IT.empty 0 0 [] doc.P.entries in
    let diagnostic =
      match result with
      | Prep.EntriesRejected reason ->
        (match reason with
         | P.DocumentRejected _ _ _ -> reason
         | P.DocumentChecked _ _ -> P.DocumentRejected P.ProofEntry None None)
      | Prep.EntriesChecked facts pending unmet ->
        (match IT.find facts doc.P.root with
         | None -> P.DocumentRejected P.MissingRoot None None
         | Some fact ->
           if fact.U.conclusion = U.Holds Z3ClauseSyntax.false_expr && fact.U.hypotheses = []
           then P.DocumentChecked pending unmet
           else P.DocumentRejected P.OpenRoot None None) in
    diagnostic, memo
