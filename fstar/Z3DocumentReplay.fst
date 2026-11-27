module Z3DocumentReplay

open Z3AstTheory
open Z3UnifiedProofSyntax
open Z3DocumentSyntax
open Z3DocumentPreparation
open Z3ProofIndex
module D = Z3DefinitionRecognition
module SK = Z3SkolemSyntax
module IT = Z3IdTable
module L = FStar.List.Tot

type entry_checker =
  list SK.definition -> bool -> bool -> list D.definition -> list judgment ->
  (judgment -> bool) -> IT.t checked_fact -> entry -> Tot (option (checked_fact & nat))

let rec diagnose_entries_using (check:entry_checker) (skolems:list SK.definition)
                               (bound:bool) (defs:list D.definition)
                               (inputs:list judgment) (contains:judgment -> bool)
                               (cache:IT.t checked_fact) (next pending:nat)
                               (unmet:list unmet_obligation) (entries:list entry)
  : Tot entries_diagnostic (decreases entries) =
  match entries with
  | [] -> EntriesChecked cache pending (L.rev unmet)
  | e :: rest ->
    match check skolems true bound defs inputs contains cache e with
    | None -> EntriesRejected (DocumentRejected ProofEntry (Some next) (Some e.formula))
    | Some (fact, local) ->
      (* Read premises before the potentially in-place table update. *)
      if local = 0 then
        diagnose_entries_using check skolems bound defs inputs contains (IT.put cache next fact)
          (next + 1) pending unmet rest
      else
        match opt_map_tail (IT.find cache) e.premise_ids with
        | None -> EntriesRejected (DocumentRejected MissingPremise (Some next) (Some e.formula))
        | Some premises ->
          let obligation = {
            obligation_index = next; obligation_rule = e.rule;
            obligation_conclusion = fact.conclusion;
            obligation_premises = premise_judgments premises;
            obligation_source = e.formula; obligation_count = local;
          } in
          diagnose_entries_using check skolems bound defs inputs contains (IT.put cache next fact)
            (next + 1) (pending + local) (obligation :: unmet) rest
