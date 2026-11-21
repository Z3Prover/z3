module Z3DocumentReplaySemanticsTests

open Z3AstTheory
module U = Z3UnifiedProofSyntax
module P = Z3DocumentPreparation
module R = Z3DocumentReplay
module RS = Z3DocumentReplaySemantics
module F = Z3DocumentFactSemantics
module IT = Z3IdTable

let atom = Var 0 bool_sort
let fact : U.checked_fact = { U.conclusion = U.Holds atom; U.hypotheses = [] }
let accepted : P.entry = { P.rule = U.Reflexivity; P.formula = atom; P.premise_ids = [] }
let pending : P.entry = { P.rule = U.Symmetry; P.formula = atom; P.premise_ids = [] }
let good (f:U.checked_fact) : prop = f == fact

let check : R.entry_checker =
  fun _ _ _ _ _ _ _ entry -> Some (fact, (if entry.P.rule = U.Reflexivity then 0 else 1))

let checked_replay ()
  : Lemma (F.table_holds good (IT.put (IT.put IT.empty 0 fact) 1 fact)) =
  F.lemma_empty good;
  assert_norm (RS.entry_sound good check [] false [] [] (fun _ -> false) [accepted; accepted]);
  assert_norm (R.diagnose_entries_using check [] false [] [] (fun _ -> false)
                 IT.empty 0 0 [] [accepted; accepted] ==
               P.EntriesChecked (IT.put (IT.put IT.empty 0 fact) 1 fact) 0 []);
  RS.lemma_checked good check [] false [] [] (fun _ -> false) IT.empty 0 []
    [accepted; accepted] (IT.put (IT.put IT.empty 0 fact) 1 fact) []

let pending_replay ()
  : Lemma (match R.diagnose_entries_using check [] false [] [] (fun _ -> false)
                   IT.empty 0 0 [] [pending] with
           | P.EntriesChecked _ n _ -> n == 1
           | P.EntriesRejected _ -> False) =
  assert_norm (R.diagnose_entries_using check [] false [] [] (fun _ -> false)
                 IT.empty 0 0 [] [pending] ==
               P.EntriesChecked (IT.put IT.empty 0 fact) 1 [{
                 P.obligation_index = 0; obligation_rule = U.Symmetry;
                 obligation_conclusion = U.Holds atom; obligation_premises = [];
                 obligation_source = atom; obligation_count = 1
               }])
