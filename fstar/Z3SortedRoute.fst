(*
   Z3SortedRoute.fst

   The Sorted/datatype document check with the scope guard of an opt-in
   accounting mode: the entries and document checks of `Z3SortedProof`
   (`check_node_cached`, `check_entries`, `check_document`,
   `diagnose_entries`, `diagnose_document`, and their epsilon-route
   composition `check_document_epsilon` / `diagnose_document_epsilon`), with
   the premise-free quantifier introduction of an NNF or quant-intro root
   replayed by `Z3NnfReplayChecked.replay_route` in place of
   `Z3NnfReplay.replay`.

   Nothing of `Z3SortedProof` is changed: the default route is the
   unchanged module, and `lemma_default_node` shows that its node check is
   `check_node_with` at the default replay verdict. The route differs from
   the default in exactly one input of the node check, the verdict of the
   certificate replay, so everything else (premises looked up among earlier
   entries, the other rules, the epsilon and dependent elaboration, the root
   fact) is the default's own code over the same typed Root model.

   Companions. The route of entry `i` is `DagV1 (DD.preparation_of cs i)`:
   the preparation the marshaler recorded for the quantifier introduction it
   marshaled as entry `i` (`Z3NativeProof.marshal_binder`, which stores the
   prepared certificate as that entry's rule). `lemma_elaborated_entry`
   proves that the epsilon elaboration keeps every entry's index, formula,
   premise ids and quantifier-introduction certificate, so the index of an
   elaborated entry is the index the companion was recorded under. The
   replayed certificate is the companion's own (`p.pcert`), whose graph and
   handles the type `DD.prepared` earns; its conclusion must be the root of
   its own classified cache AND the node's conclusion (`RootMismatch`
   otherwise), and a replayed node is a theorem of the same typed model
   whatever certificate was replayed (`NRC.lemma_replay_route`). No
   comparison of the node's certificate with the companion's is made or
   needed for soundness; it decides only which certificate is replayed, so
   a stale or foreign companion leaves a node pending or its replay
   unsuccessful, never certifies a false conclusion.

   A route whose preparation is missing (clausal, absent, exhausted, invalid)
   leaves the node pending, with the reason in the additive report; the
   default guard never runs in its place.
*)
module Z3SortedRoute

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module DT = Z3SortedDatatype
module U = Z3UnifiedProof
module P = Z3ProofDocument
module R = Z3ResolutionProofTheory
module L = FStar.List.Tot
module I = Z3ProofIndex
module IT = Z3IdTable
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module NR = Z3NnfReplay
module NRC = Z3NnfReplayChecked
module SP = Z3SortedProof
module DD = Z3DagDocument
module VD = Z3VerifiedDocument
module G = Z3CheckedGuard
module CT = Z3CheckedTerms
module AR = Z3SortedArithmetic
module B = Z3BoundedBoolEquiv

(* ---------------------------------------------------------------------- *)
(* 1. The node check with a given replay verdict                            *)
(* ---------------------------------------------------------------------- *)

(* The replay of a node's certificate under a route: `SP.nnf_verdict` for
   the default route, the route's replay otherwise. Only a premise-free
   quantifier introduction is replayed. *)
let nnf_result (r:NRC.route) (assertions:list expr) (node:U.proof_node) : NRC.result =
  match node.U.kind with
  | U.QuantifierIntroduction c ->
    if Nil? node.U.premises then NRC.replay_route r assertions c node.U.conclusion
    else { NRC.verdict = NR.Unreplayed; NRC.outcome = NRC.NotConsumed }
  | _ -> { NRC.verdict = NR.Unreplayed; NRC.outcome = NRC.NotConsumed }

(* `SP.check_node_cached` with the replay verdict `nnf` given. *)
let check_node_with (s:S.checked_schema) (assertions:list expr) (node:U.proof_node) (nnf:NR.verdict)
  : option (U.checked_fact & nat) =
  let conclusion = SP.proposition node.U.conclusion in
  if not (SP.boolean_expression s conclusion) then None
  else match node.U.kind with
  | U.Asserted ->
    if node.U.premises = [] && L.mem conclusion assertions
    then Some ({ U.conclusion = node.U.conclusion; hypotheses = [] }, 0)
    else None
  | U.Hypothesis ->
    if node.U.premises = []
    then Some ({ U.conclusion = node.U.conclusion; hypotheses = [conclusion] }, 0)
    else None
  | _ ->
    if nnf = NR.Malformed then None else
    let inherited = U.premise_hypotheses node.U.premises in
    let hypotheses =
      if SP.lemma_step node then
        match node.U.premises with [p] -> SP.remaining_hypotheses p.hypotheses conclusion | _ -> inherited
      else if node.U.kind = U.LemmaRule then U.remaining_hypotheses inherited conclusion
      else inherited in
    let fact = { U.conclusion = node.U.conclusion; hypotheses = hypotheses } in
    let checked =
      SP.arithmetic_farkas node || SP.quantifier_instantiation node || SP.quantifier_flattening node ||
      SP.lemma_step node ||
      nnf = NR.Replayed ||
      (node.U.kind <> U.LemmaRule && SP.consequence s (SP.propositions node.U.premises) conclusion) ||
      DT.consequence s (SP.scoped_propositions node.U.premises) (SP.scoped_proposition fact) ||
      (node.U.kind <> U.LemmaRule && SP.linear_consequence (SP.propositions node.U.premises) conclusion) in
    Some (fact, (if checked then 0 else 1))

(* The default node check is the node check at the default replay verdict. *)
let lemma_default_node (s:S.checked_schema) (assertions:list expr) (node:U.proof_node)
  : Lemma (SP.check_node_cached s assertions node ==
           check_node_with s assertions node (SP.nnf_verdict assertions node)) = ()

let lemma_default_replay (assertions:list expr) (node:U.proof_node)
  : Lemma ((nnf_result NRC.Default assertions node).NRC.verdict == SP.nnf_verdict assertions node) = ()

let check_node_route (s:S.checked_schema) (r:NRC.route) (assertions:list expr) (node:U.proof_node)
  : option (U.checked_fact & nat) =
  check_node_with s assertions node (nnf_result r assertions node).NRC.verdict

let lemma_check_node_context_with (s:S.checked_schema) (assertions:list expr)
                                  (node:U.proof_node) (fact:U.checked_fact) (pending:nat) (nnf:NR.verdict)
  : Lemma (requires SP.facts_valid s node.U.premises /\
                    check_node_with s assertions node nnf == Some (fact, pending))
          (ensures SP.fact_valid s fact) =
  match node.U.kind with
  | U.Asserted | U.Hypothesis -> ()
  | _ ->
    SP.lemma_premise_context s node.U.premises;
    if SP.lemma_step node then (
      match node.U.premises with
      | [p] -> SP.lemma_remaining_context s p.hypotheses (SP.proposition node.U.conclusion)
      | _ -> ())
    else if node.U.kind = U.LemmaRule then
      SP.lemma_remaining_context s (U.premise_hypotheses node.U.premises) (SP.proposition node.U.conclusion)

(* A replayed node: its conclusion, a closed equation of two values, is true
   (`NRC.lemma_replay_route` at the scope [] and the empty environment). *)
let lemma_nnf_route_node (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                         (r:NRC.route) (assertions:list expr) (node:U.proof_node)
  : Lemma (requires T.truths s bc eq other assertions /\
                    (U.QuantifierIntroduction? node.U.kind ==> Q.forall_model s bc other /\ E.exists_model s bc other) /\
                    SP.boolean_expression s (SP.proposition node.U.conclusion) /\
                    (nnf_result r assertions node).NRC.verdict == NR.Replayed)
          (ensures T.truth s bc eq other (SP.proposition node.U.conclusion)) =
  match node.U.kind with
  | U.QuantifierIntroduction c ->
    NRC.lemma_replay_route s bc eq other r assertions c node.U.conclusion;
    (match node.U.conclusion with
     | U.Equal a b | U.Observational a b ->
       V.lemma_sort_eq (get_sort b) (get_sort a);
       T.lemma_same_value s bc eq other a b;
       T.lemma_equality s bc eq other a b
     | U.Holds _ -> ())
  | _ -> ()

let lemma_check_node_with (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                          (assertions:list expr) (node:U.proof_node) (fact:U.checked_fact) (nnf:NR.verdict)
  : Lemma (requires T.truths s bc eq other assertions /\ SP.facts_hold s bc eq other node.U.premises /\
                    SP.facts_valid s node.U.premises /\
                    (SP.quantifier_instantiation node ==> Q.forall_elimination_model s bc other) /\
                    (SP.quantifier_flattening node ==> Q.forall_model s bc other) /\
                    (U.QuantifierIntroduction? node.U.kind ==> Q.forall_model s bc other /\ E.exists_model s bc other) /\
                    (nnf == NR.Replayed ==> T.truth s bc eq other (SP.proposition node.U.conclusion)) /\
                    check_node_with s assertions node nnf == Some (fact, 0))
          (ensures SP.fact_holds s bc eq other fact) =
  lemma_check_node_context_with s assertions node fact 0 nnf;
  match node.U.kind with
  | U.Asserted -> SP.lemma_truth_member s bc eq other assertions (SP.proposition node.U.conclusion)
  | U.Hypothesis -> ()
  | _ ->
    let conclusion = SP.proposition node.U.conclusion in
    if SP.arithmetic_farkas node then (
      if T.truths s bc eq other fact.hypotheses && not (T.truth s bc eq other conclusion) then (
        SP.lemma_premise_hypotheses s bc eq other node.U.premises;
        DT.lemma_literals s bc eq other conclusion;
        SP.lemma_arithmetic_assumptions s bc eq other (SP.propositions node.U.premises) (DT.literals conclusion);
        match node.U.kind with
        | U.ArithmeticFarkas cs ->
          AR.lemma_check_contradiction s bc eq other (SP.arithmetic_assumptions node) cs
        | _ -> ()))
    else if SP.quantifier_instantiation node then (
      match node.U.kind, node.U.conclusion with
      | U.QuantifierInstantiation args, U.Holds formula ->
        Q.lemma_check s bc eq other args formula
      | _, _ -> ())
    else if SP.quantifier_flattening node then
      Q.lemma_check_flatten s bc eq other conclusion
    else if SP.lemma_step node then (
      match node.U.premises with
      | [p] ->
        if T.truths s bc eq other fact.hypotheses && not (T.truth s bc eq other conclusion) then (
          SP.lemma_remaining_hypotheses s bc eq other p.hypotheses conclusion;
          assert_norm (T.cut 1 R.false_expr == B.Bool false);
          T.lemma_cut s bc eq other 1 R.false_expr)
      | _ -> ())
    else if nnf = NR.Replayed then ()
    else if node.U.kind <> U.LemmaRule && SP.consequence s (SP.propositions node.U.premises) conclusion then (
      if T.truths s bc eq other fact.hypotheses then (
        SP.lemma_premise_hypotheses s bc eq other node.U.premises;
        SP.lemma_consequence s bc eq other (SP.propositions node.U.premises) conclusion))
    else if DT.consequence s (SP.scoped_propositions node.U.premises) (SP.scoped_proposition fact) then (
      SP.lemma_scoped_propositions s bc eq other node.U.premises;
      DT.lemma_consequence s bc eq other (SP.scoped_propositions node.U.premises) (SP.scoped_proposition fact);
      SP.lemma_scoped_proposition s bc eq other fact)
    else (
      if T.truths s bc eq other fact.hypotheses then (
        SP.lemma_premise_hypotheses s bc eq other node.U.premises;
        SP.lemma_linear_consequence s bc eq other (SP.propositions node.U.premises) conclusion))

let lemma_check_node_route (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                           (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                           (r:NRC.route) (assertions:list expr) (node:U.proof_node) (fact:U.checked_fact)
  : Lemma (requires T.truths s bc eq other assertions /\ SP.facts_hold s bc eq other node.U.premises /\
                    SP.facts_valid s node.U.premises /\
                    (SP.quantifier_instantiation node ==> Q.forall_elimination_model s bc other) /\
                    (SP.quantifier_flattening node ==> Q.forall_model s bc other) /\
                    (U.QuantifierIntroduction? node.U.kind ==> Q.forall_model s bc other /\ E.exists_model s bc other) /\
                    check_node_route s r assertions node == Some (fact, 0))
          (ensures SP.fact_holds s bc eq other fact) =
  let nnf = (nnf_result r assertions node).NRC.verdict in
  if nnf = NR.Replayed && SP.boolean_expression s (SP.proposition node.U.conclusion) then
    lemma_nnf_route_node s bc eq other r assertions node;
  lemma_check_node_with s bc eq other assertions node fact nnf

(* ---------------------------------------------------------------------- *)
(* 2. The entries and the document                                          *)
(* ---------------------------------------------------------------------- *)

(* The route of entry `next`: the preparation recorded for it. *)
let entry_route (cs:DD.companions) (next:nat) : NRC.route = NRC.DagV1 (DD.preparation_of cs next)

let rec check_entries_route (cs:DD.companions) (s:S.checked_schema) (assertions:list expr)
                            (cache:I.index_tree U.checked_fact) (next pending:nat) (entries:list P.entry)
  : Tot (option (I.index_tree U.checked_fact & nat)) (decreases entries) =
  match entries with
  | [] -> Some (cache, pending)
  | e :: rest ->
    (match SP.prepare_entry s cache e with
     | None -> None
     | Some node ->
       (match check_node_route s (entry_route cs next) assertions node with
        | None -> None
        | Some (fact, local) ->
          check_entries_route cs s assertions (I.index_put cache next fact) (next + 1) (pending + local) rest))

let check_document_route (cs:DD.companions) (schema:S.schema) (doc:P.document) : option nat =
  if not (S.valid schema) then None
  else if not (SP.boolean_expressions schema doc.assertions && U.ordinary_facts doc.assertions) then None
  else match check_entries_route cs schema doc.assertions I.Empty 0 0 doc.entries with
  | None -> None
  | Some (cache, pending) ->
    (match I.index_find cache doc.root with
     | Some fact ->
       if fact.conclusion = U.Holds R.false_expr && fact.hypotheses = [] then Some pending else None
     | None -> None)

let rec lemma_pending_route (cs:DD.companions) (s:S.checked_schema) (assertions:list expr)
                            (cache:I.index_tree U.checked_fact) (next pending:nat) (entries:list P.entry)
                            (result:I.index_tree U.checked_fact) (count:nat)
  : Lemma (requires check_entries_route cs s assertions cache next pending entries == Some (result, count))
          (ensures pending <= count)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    let node = Some?.v (SP.prepare_entry s cache e) in
    let fact, local = Some?.v (check_node_route s (entry_route cs next) assertions node) in
    lemma_pending_route cs s assertions (I.index_put cache next fact) (next + 1) (pending + local) rest result count

let rec lemma_entries_route (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (cs:DD.companions) (assertions:list expr) (cache:I.index_tree U.checked_fact)
                            (next pending:nat) (entries:list P.entry) (result:I.index_tree U.checked_fact)
  : Lemma (requires T.truths s bc eq other assertions /\ SP.cache_sound s bc eq other cache /\
                    (SP.needs_forall_semantics entries ==> Q.forall_elimination_model s bc other) /\
                    (SP.needs_forall_truth entries ==> Q.forall_model s bc other) /\
                    (SP.needs_binder_semantics entries ==> Q.forall_model s bc other /\ E.exists_model s bc other) /\
                    check_entries_route cs s assertions cache next pending entries == Some (result, 0))
          (ensures SP.cache_sound s bc eq other result)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    let node = Some?.v (SP.prepare_entry s cache e) in
    let r = entry_route cs next in
    let fact, local = Some?.v (check_node_route s r assertions node) in
    lemma_pending_route cs s assertions (I.index_put cache next fact) (next + 1) (pending + local) rest result 0;
    SP.lemma_premise_lookup s bc eq other cache e.premise_ids node.premises;
    lemma_check_node_context_with s assertions node fact local (nnf_result r assertions node).NRC.verdict;
    lemma_check_node_route s bc eq other r assertions node fact;
    SP.lemma_cache_insert s bc eq other cache next fact;
    lemma_entries_route s bc eq other cs assertions (I.index_put cache next fact) (next + 1)
      (pending + local) rest result

let lemma_check_document_route (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                               (cs:DD.companions) (doc:P.document)
  : Lemma (requires check_document_route cs s doc == Some 0 /\
                    (SP.needs_forall_semantics doc.entries ==> Q.forall_elimination_model s bc other) /\
                    (SP.needs_forall_truth doc.entries ==> Q.forall_model s bc other) /\
                    (SP.needs_binder_semantics doc.entries ==> Q.forall_model s bc other /\ E.exists_model s bc other))
          (ensures not (T.truths s bc eq other doc.assertions)) =
  if T.truths s bc eq other doc.assertions then (
    let cache, _ = Some?.v (check_entries_route cs s doc.assertions I.Empty 0 0 doc.entries) in
    lemma_entries_route s bc eq other cs doc.assertions I.Empty 0 0 doc.entries cache;
    assert (doc.root >= 0);
    let root = Some?.v (I.index_find cache doc.root) in
    assert (I.index_get cache doc.root == Some root);
    assert (SP.fact_valid s root /\ SP.fact_holds s bc eq other root);
    assert (T.truth s bc eq other R.false_expr);
    assert_norm (T.cut 1 R.false_expr == B.Bool false);
    T.lemma_cut s bc eq other 1 R.false_expr)

(* ---------------------------------------------------------------------- *)
(* 3. The diagnosed check                                                   *)
(* ---------------------------------------------------------------------- *)

(* The additive report of one replayed certificate (an NNF or quant-intro
   root of a premise-free quantifier introduction), in the rows of the
   opt-in mode. Applied: the guard ran (checked, refused or exhausted with its
   phase, the Skolem typing gate exhausting the validation allowance) or the
   certificate's own entries were not accepted (`BinderEntriesFailed`: a
   formula the replay cannot classify, a conclusion that is not the node's
   root, or a local rule it rejects). Not applied: the preparation is
   missing, with the reason (`BinderUnprepared`). A certificate the replay
   does not consume has no row. *)
let route_report (next:nat) (node:U.proof_node) (prep:DD.preparation) (res:NRC.result)
  : option VD.binder_report =
  let n = VD.entry_count node.U.kind in
  let graph, why = match prep with DD.Ready _ u -> Some u, None | DD.Unready w u -> u, Some w in
  let report (o:G.binder_outcome) : option VD.binder_report =
    Some ({ VD.report_index = next; VD.report_entries = n; VD.report_outcome = o; VD.report_graph = graph;
            VD.report_unprepared = why; VD.report_debit = None; VD.report_forfeit = None }) in
  match res.NRC.outcome with
  | NRC.DefaultRoute -> None
  | NRC.NotConsumed -> None
  | NRC.GuardChecked left -> report (G.BinderGuardChecked left)
  | NRC.GuardRefused -> report (G.BinderGuardRefused (DD.dag_budget n))
  | NRC.GuardExhausted ph -> report (G.BinderGuardExhausted ph)
  | NRC.SkolemTypingExhausted -> report (G.BinderGuardExhausted CT.Validation)
  | NRC.Unprepared _ -> report G.BinderUnprepared
  | NRC.MalformedPremises -> report G.BinderEntriesFailed
  | NRC.EntriesUnclassified -> report G.BinderEntriesFailed
  | NRC.RootMismatch -> report G.BinderEntriesFailed
  | NRC.StepsFailed _ -> report G.BinderEntriesFailed

let rec diagnose_entries_route (cs:DD.companions) (s:S.checked_schema) (assertions:list expr)
                               (cache:IT.t U.checked_fact) (next pending:nat)
                               (unmet:list P.unmet_obligation) (reports:list VD.binder_report)
                               (entries:list P.entry)
  : Tot (P.entries_diagnostic & list VD.binder_report) (decreases entries) =
  match entries with
  | [] -> P.EntriesChecked cache pending (L.rev unmet), L.rev reports
  | e :: rest ->
    let reject = P.EntriesRejected (P.DocumentRejected P.ProofEntry (Some next) (Some e.formula)) in
    match SP.prepare_entry_table s cache e with
    | None -> reject, L.rev reports
    | Some node ->
      let prep = DD.preparation_of cs next in
      let res = nnf_result (NRC.DagV1 prep) assertions node in
      let reports = match route_report next node prep res with Some r -> r :: reports | None -> reports in
      (match check_node_with s assertions node res.NRC.verdict with
       | None -> reject, L.rev reports
       | Some (fact, local) ->
         let cache = IT.put cache next fact in
         let unmet =
           if local = 0 then unmet
           else {
             P.obligation_index = next; obligation_rule = e.rule;
             obligation_conclusion = fact.conclusion;
             obligation_premises = U.premise_judgments node.premises;
             obligation_source = e.formula; obligation_count = local;
           } :: unmet in
         diagnose_entries_route cs s assertions cache (next + 1) (pending + local) unmet reports rest)

let rec lemma_diagnose_entries_route (cs:DD.companions) (s:S.checked_schema) (assertions:list expr)
                                     (cache:IT.t U.checked_fact) (tree:I.index_tree U.checked_fact)
                                     (next pending:nat) (unmet:list P.unmet_obligation)
                                     (reports:list VD.binder_report) (entries:list P.entry)
  : Lemma (requires P.agrees cache tree)
          (ensures P.entries_agree
                     (SP.diagnostic_entries_result (fst (diagnose_entries_route cs s assertions cache next pending unmet reports entries)))
                     (check_entries_route cs s assertions tree next pending entries))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    P.lemma_agrees_opt_map cache tree e.premise_ids;
    (match SP.prepare_entry_table s cache e with
     | None -> ()
     | Some node ->
       (match check_node_route s (entry_route cs next) assertions node with
        | None -> ()
        | Some (fact, local) ->
          let prep = DD.preparation_of cs next in
          let res = nnf_result (NRC.DagV1 prep) assertions node in
          let reports = match route_report next node prep res with Some r -> r :: reports | None -> reports in
          let unmet =
            if local = 0 then unmet
            else {
              P.obligation_index = next; obligation_rule = e.rule;
              obligation_conclusion = fact.conclusion;
              obligation_premises = U.premise_judgments node.premises;
              obligation_source = e.formula; obligation_count = local;
            } :: unmet in
          P.lemma_agrees_put cache tree next fact;
          lemma_diagnose_entries_route cs s assertions (IT.put cache next fact) (I.index_put tree next fact)
            (next + 1) (pending + local) unmet reports rest))

let diagnose_document_route (cs:DD.companions) (schema:S.schema) (doc:P.document) : VD.verified_diagnostic =
  if not (S.valid schema) then
    { VD.diagnostic = P.DocumentRejected P.LogicalDeclarations None None; VD.reports = [] }
  else if not (SP.boolean_expressions schema doc.assertions && U.ordinary_facts doc.assertions) then
    { VD.diagnostic = P.DocumentRejected P.OriginalAssertions None None; VD.reports = [] }
  else
    let entries, reports = diagnose_entries_route cs schema doc.assertions IT.empty 0 0 [] [] doc.entries in
    let diagnostic =
      match entries with
      | P.EntriesRejected reason ->
        (match reason with
         | P.DocumentRejected _ _ _ -> reason
         | P.DocumentChecked _ _ -> P.DocumentRejected P.ProofEntry None None)
      | P.EntriesChecked cache pending unmet ->
        (match IT.find cache doc.root with
         | None -> P.DocumentRejected P.MissingRoot None None
         | Some fact ->
           if fact.conclusion = U.Holds R.false_expr && fact.hypotheses = []
           then P.DocumentChecked pending unmet else P.DocumentRejected P.OpenRoot None None) in
    { VD.diagnostic = diagnostic; VD.reports = reports }

(* The verdict of a diagnosed document is the verdict of its check: one
   diagnosed check serves stdout, the exit status and the rows. *)
let lemma_diagnose_document_route (cs:DD.companions) (schema:S.schema) (doc:P.document)
  : Lemma (SP.diagnostic_result (diagnose_document_route cs schema doc).VD.diagnostic ==
           check_document_route cs schema doc) =
  if S.valid schema && SP.boolean_expressions schema doc.assertions && U.ordinary_facts doc.assertions
  then (
    lemma_diagnose_entries_route cs schema doc.assertions IT.empty I.Empty 0 0 [] [] doc.entries;
    match diagnose_entries_route cs schema doc.assertions IT.empty 0 0 [] [] doc.entries with
    | P.EntriesRejected reason, _ ->
      (match reason with P.DocumentRejected _ _ _ | P.DocumentChecked _ _ -> ())
    | P.EntriesChecked cache _ _, _ ->
      (match IT.find cache doc.root with None -> () | Some _ -> ()))

(* ---------------------------------------------------------------------- *)
(* 4. The epsilon route                                                     *)
(* ---------------------------------------------------------------------- *)

let check_document_epsilon_route (cs:DD.companions) (schema:S.schema) (doc:P.document) : option nat =
  if not (S.valid schema) then None
  else check_document_route cs schema (SP.elaborate_full schema doc)

let diagnose_document_epsilon_route (cs:DD.companions) (schema:S.schema) (doc:P.document)
  : VD.verified_diagnostic =
  if not (S.valid schema) then
    { VD.diagnostic = P.DocumentRejected P.LogicalDeclarations None None; VD.reports = [] }
  else diagnose_document_route cs schema (SP.elaborate_full schema doc)

let lemma_diagnose_document_epsilon_route (cs:DD.companions) (schema:S.schema) (doc:P.document)
  : Lemma (SP.diagnostic_result (diagnose_document_epsilon_route cs schema doc).VD.diagnostic ==
           check_document_epsilon_route cs schema doc) =
  if S.valid schema then
    lemma_diagnose_document_route cs schema (SP.elaborate_full schema doc)

(* The route's document theorem, for the SAME model construction as the
   default epsilon route (`SP.full_extension`: one consistent extension of
   the original model by the used closed and dependent definitions): the
   elaborated assertions hold in the extension exactly when the original
   ones hold in `other`, and the route's check is a refutation of them. *)
let lemma_check_document_epsilon_route (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                                       (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                                       (other:V.interpretation base (S.signature s))
                                       (cs:DD.companions) (doc:P.document)
  : Lemma (requires check_document_epsilon_route cs s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other)
          (ensures not (T.truths s bc eq other doc.assertions)) =
  if T.truths s bc eq other doc.assertions then (
    let j = SP.full_extension s bc eq choice doc other in
    SP.lemma_full_extension s bc eq choice doc other;
    SP.lemma_full_forall_elimination s bc j;
    lemma_check_document_route s bc eq j cs (SP.elaborate_full s doc))

(* ---------------------------------------------------------------------- *)
(* 5. The companions of the elaborated document                             *)
(* ---------------------------------------------------------------------- *)

(* Only a used Skolemization step is rewritten (to Asserted): a quantifier
   introduction is never an epsilon entry. *)
let lemma_epsilon_entry_rule (s:S.checked_schema) (ds:list (E.definition s)) (e:P.entry)
  : Lemma (requires SP.epsilon_entry s ds e) (ensures e.P.rule == U.Skolemization) = ()

(* The elaborated document has the original's entries at the same indices,
   with the same formulas and premise ids, and a quantifier introduction
   keeps its certificate: the entry a companion was recorded under (its
   marshal-time index) is the entry the route reads, with the certificate the
   marshaler stored. Elaboration only appends equations and closures to the
   assertions. *)
let lemma_elaborated_entry (s:S.checked_schema) (doc:P.document) (n:nat)
  : Lemma (requires n < L.length doc.P.entries)
          (ensures L.length (SP.elaborate_full s doc).P.entries == L.length doc.P.entries /\
                   (let e = L.index doc.P.entries n in
                    let e' = L.index (SP.elaborate_full s doc).P.entries n in
                    e'.P.formula == e.P.formula /\ e'.P.premise_ids == e.P.premise_ids /\
                    (U.QuantifierIntroduction? e.P.rule ==> e'.P.rule == e.P.rule))) =
  let ds = SP.epsilon_context s doc in
  if ds <> [] then (
    SP.lemma_epsilon_entries_aligned s ds doc.P.entries n;
    let e = L.index doc.P.entries n in
    if SP.epsilon_entry s ds e then lemma_epsilon_entry_rule s ds e)
