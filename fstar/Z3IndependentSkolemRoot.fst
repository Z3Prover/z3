module Z3IndependentSkolemRoot

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module D = Z3DefinitionSyntax
module U = Z3UnifiedProofSyntax
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module Cached = Z3IndependentCachedReplay
module SR = Z3SortedRoot
module RL = Z3SortedReal
module RR = Z3SortedRealRoot
module DR = Z3SortedDivisionRoot
module DS = Z3SortedDependentSkolem
module SP = Z3SortedProof
module Replay = Z3IndependentSkolemReplay
module DReplay = Z3IndependentDependentReplay
module Model = Z3IndependentSkolemModel
module Binder = Z3IndependentBinderElaboration
module L = FStar.List.Tot

let dependent_closures (larger:bool) (schema:S.schema) (doc:P.document) : list Z3AstTheory.expr =
  if S.valid schema then
    let ds = Replay.context schema doc in
    DS.closures schema (if larger then DReplay.context schema doc ds
                        else SP.dependent_context schema doc ds)
  else []

let check_with (larger:bool) (schema:S.schema) (doc:P.document) : Root.root_verdict =
  match (if larger then Model.check_dependent schema doc else Model.check schema doc) with
  | None -> Root.RootRejected
  | Some n ->
    if n > 0 then Root.RootPending n
    else if Root.root_covered schema doc &&
            TR.supported_expressions (S.signature schema) (dependent_closures larger schema doc)
    then Root.RootCertified
    else Root.RootUncovered

let check (schema:S.schema) (doc:P.document) : Root.root_verdict = check_with false schema doc
let check_dependent (schema:S.schema) (doc:P.document) : Root.root_verdict = check_with true schema doc

let rec binder_entries_covered (schema:S.checked_schema) (assertions:list Z3AstTheory.expr)
                               (entries:list P.entry)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | e :: rest ->
    let sigma = S.signature schema in
    let covered = Root.entry_covered sigma e ||
      (D.scoped [] e.P.formula && TR.supported_expression sigma e.P.formula &&
       D.scoped_args [] (Root.rule_terms e.P.rule) &&
       TR.supported_expressions sigma (Root.rule_terms e.P.rule) &&
       (match e.P.rule with
        | U.QuantifierIntroduction c ->
          Root.binder_entries_covered sigma c.U.binder_entries &&
          Some? (Binder.candidate schema assertions e)
        | _ -> false)) in
    covered && binder_entries_covered schema assertions rest

let binder_root_covered (schema:S.checked_schema) (doc:P.document) : bool =
  let expanded = Model.elaborate_dependent schema doc in
  TR.supported schema &&
  D.scoped_args [] doc.P.assertions &&
  TR.supported_expressions (S.signature schema) doc.P.assertions &&
  binder_entries_covered schema expanded.P.assertions doc.P.entries

let rec binder_entries_covered_selected (schema:S.checked_schema) (expanded:P.document)
                                        (selected:list P.entry) (entries:list P.entry)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | e :: rest ->
    let sigma = S.signature schema in
    let covered = Root.entry_covered sigma e ||
      (D.scoped [] e.P.formula && TR.supported_expression sigma e.P.formula &&
       D.scoped_args [] (Root.rule_terms e.P.rule) &&
       TR.supported_expressions sigma (Root.rule_terms e.P.rule) &&
       (match e.P.rule with
        | U.QuantifierIntroduction c ->
          Root.binder_entries_covered sigma c.U.binder_entries &&
          (if L.mem e expanded.P.entries then L.mem e selected
           else Some? (Binder.candidate schema expanded.P.assertions e))
        | _ -> false)) in
    covered && binder_entries_covered_selected schema expanded selected rest

let binder_root_covered_selected (schema:S.checked_schema) (doc expanded:P.document)
                                 (selected:list P.entry) : bool =
  TR.supported schema &&
  D.scoped_args [] doc.P.assertions &&
  TR.supported_expressions (S.signature schema) doc.P.assertions &&
  binder_entries_covered_selected schema expanded selected doc.P.entries

let rec lemma_entries_covered_selected (schema:S.checked_schema) (expanded:P.document)
                                       (entries:list P.entry)
  : Lemma (ensures binder_entries_covered_selected schema expanded
                     (snd (Binder.augment_with_selection schema expanded)) entries ==
                   binder_entries_covered schema expanded.P.assertions entries)
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    Binder.lemma_selection schema expanded e;
    lemma_entries_covered_selected schema expanded rest

let lemma_root_covered_selected (schema:S.checked_schema) (doc:P.document)
  : Lemma (let expanded = Model.elaborate_dependent schema doc in
           binder_root_covered_selected schema doc expanded
             (snd (Binder.augment_with_selection schema expanded)) ==
           binder_root_covered schema doc) =
  lemma_entries_covered_selected schema (Model.elaborate_dependent schema doc) doc.P.entries

let check_binder_reference (schema:S.schema) (doc:P.document) : GTot Root.root_verdict =
  match Model.check_binder schema doc with
  | None -> Root.RootRejected
  | Some n ->
    if n > 0 then Root.RootPending n
    else if S.valid schema && binder_root_covered schema doc &&
            TR.supported_expressions (S.signature schema) (dependent_closures true schema doc)
    then Root.RootCertified
    else Root.RootUncovered

let check_binder_with (require_selection:bool) (schema:S.schema) (doc:P.document) : Root.root_verdict =
  if not (S.valid schema) then Root.RootRejected
  else
    let expanded = Model.elaborate_dependent schema doc in
    let augmented, selected = Binder.augment_with_selection schema expanded in
    if require_selection && selected = [] then Root.RootPending 1
    else if require_selection && not (binder_root_covered_selected schema doc expanded selected)
    then Root.RootUncovered
    else match Cached.check_document schema augmented with
    | None -> Root.RootRejected
    | Some n ->
      if n > 0 then Root.RootPending n
      else if (require_selection || binder_root_covered_selected schema doc expanded selected) &&
              TR.supported_expressions (S.signature schema) (dependent_closures true schema doc)
      then Root.RootCertified
      else Root.RootUncovered

let check_binder (schema:S.schema) (doc:P.document) : Root.root_verdict =
  check_binder_with false schema doc

let check_binder_selected (schema:S.schema) (doc:P.document) : bool =
  check_binder_with true schema doc = Root.RootCertified

let lemma_check_binder_reference (schema:S.schema) (doc:P.document)
  : Lemma (check_binder schema doc == check_binder_reference schema doc) =
  if S.valid schema then lemma_root_covered_selected schema doc

let contexts_may_differ (schema:S.schema) (doc:P.document) : bool =
  if S.valid schema then DReplay.may_change schema doc else false

let lemma_same_context_verdict (schema:S.checked_schema) (doc:P.document)
  : Lemma (requires not (contexts_may_differ schema doc))
          (ensures check_dependent schema doc == check schema doc) =
  DReplay.lemma_unchanged schema doc (Replay.context schema doc);
  Model.lemma_same_dependent_context schema doc

let lemma_certified_with (larger:bool) (u:TR.uninterpreted) (schema:S.checked_schema)
                    (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_with larger schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  Root.lemma_forall_model u schema model;
  Root.lemma_exists_model u schema model;
  if RL.real_primitive schema then RR.lemma_root_real_model u schema model;
  DR.lemma_root_division_laws u schema model;
  (if larger then
    Model.lemma_check_dependent schema (TR.booleans u) (SR.root_scalars u) (Root.root_choice u schema) model doc
  else
    Model.lemma_check schema (TR.booleans u) (SR.root_scalars u) (Root.root_choice u schema) model doc);
  Root.lemma_truths_agreement u schema model doc.P.assertions

let lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
                    (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  lemma_certified_with false u schema doc model

let lemma_certified_dependent (u:TR.uninterpreted) (schema:S.checked_schema)
                              (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_dependent schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  lemma_certified_with true u schema doc model

let lemma_certified_binder (u:TR.uninterpreted) (schema:S.checked_schema)
                           (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_binder schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  lemma_check_binder_reference schema doc;
  Root.lemma_forall_model u schema model;
  Root.lemma_exists_model u schema model;
  if RL.real_primitive schema then RR.lemma_root_real_model u schema model;
  DR.lemma_root_division_laws u schema model;
  Model.lemma_check_binder schema (TR.booleans u) (SR.root_scalars u) (Root.root_choice u schema) model doc;
  Root.lemma_truths_agreement u schema model doc.P.assertions

let lemma_certified_binder_selected (u:TR.uninterpreted) (schema:S.checked_schema)
                           (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_binder_selected schema doc /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  lemma_certified_binder u schema doc model
