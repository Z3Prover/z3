module Z3DocumentReplaySemantics

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module P = Z3DocumentPreparation
module Replay = Z3DocumentReplay
module F = Z3DocumentFactSemantics
module D = Z3DefinitionRecognition
module SK = Z3SkolemSyntax
module IT = Z3IdTable
module L = FStar.List.Tot

let entry_sound (good:U.checked_fact -> prop) (check:Replay.entry_checker)
                (skolems:list SK.definition) (bound:bool) (defs:list D.definition)
                (inputs:list U.judgment) (contains:U.judgment -> bool)
                (entries:list P.entry) : prop =
  forall (table:IT.t U.checked_fact) (entry:P.entry) (fact:U.checked_fact).
    L.mem entry entries /\ F.table_holds good table /\
    check skolems true bound defs inputs contains table entry == Some (fact, 0) ==> good fact

let rec lemma_pending (check:Replay.entry_checker) (skolems:list SK.definition)
                      (bound:bool) (defs:list D.definition)
                      (inputs:list U.judgment) (contains:U.judgment -> bool)
                      (table:IT.t U.checked_fact) (next pending:nat)
                      (unmet:list P.unmet_obligation) (entries:list P.entry)
                      (final:IT.t U.checked_fact) (count:nat) (obligations:list P.unmet_obligation)
  : Lemma (requires Replay.diagnose_entries_using check skolems bound defs inputs contains table
                      next pending unmet entries == P.EntriesChecked final count obligations)
          (ensures pending <= count)
          (decreases entries) =
  match entries with
  | [] -> ()
  | entry :: rest ->
    match check skolems true bound defs inputs contains table entry with
    | None -> ()
    | Some (fact, local) ->
      if local = 0 then
        lemma_pending check skolems bound defs inputs contains (IT.put table next fact)
          (next + 1) pending unmet rest final count obligations
      else
        match Z3ProofIndex.opt_map_tail (IT.find table) entry.P.premise_ids with
        | None -> ()
        | Some premises ->
          let obligation = {
            P.obligation_index = next; obligation_rule = entry.P.rule;
            obligation_conclusion = fact.U.conclusion;
            obligation_premises = U.premise_judgments premises;
            obligation_source = entry.P.formula; obligation_count = local;
          } in
          lemma_pending check skolems bound defs inputs contains (IT.put table next fact)
            (next + 1) (pending + local) (obligation :: unmet) rest final count obligations

let rec lemma_checked (good:U.checked_fact -> prop) (check:Replay.entry_checker)
                      (skolems:list SK.definition) (bound:bool) (defs:list D.definition)
                      (inputs:list U.judgment) (contains:U.judgment -> bool)
                      (table:IT.t U.checked_fact) (next:nat)
                      (unmet:list P.unmet_obligation) (entries:list P.entry)
                      (final:IT.t U.checked_fact) (obligations:list P.unmet_obligation)
  : Lemma (requires F.table_holds good table /\
                    entry_sound good check skolems bound defs inputs contains entries /\
                    Replay.diagnose_entries_using check skolems bound defs inputs contains table
                      next 0 unmet entries == P.EntriesChecked final 0 obligations)
          (ensures F.table_holds good final)
          (decreases entries) =
  match entries with
  | [] -> ()
  | entry :: rest ->
    match check skolems true bound defs inputs contains table entry with
    | None -> ()
    | Some (fact, local) ->
      if local = 0 then (
        F.lemma_put good table next fact;
        lemma_checked good check skolems bound defs inputs contains (IT.put table next fact)
          (next + 1) unmet rest final obligations)
      else
        match Z3ProofIndex.opt_map_tail (IT.find table) entry.P.premise_ids with
        | None -> ()
        | Some premises ->
          let obligation = {
            P.obligation_index = next; obligation_rule = entry.P.rule;
            obligation_conclusion = fact.U.conclusion;
            obligation_premises = U.premise_judgments premises;
            obligation_source = entry.P.formula; obligation_count = local;
          } in
          lemma_pending check skolems bound defs inputs contains (IT.put table next fact)
            (next + 1) local (obligation :: unmet) rest final 0 obligations
