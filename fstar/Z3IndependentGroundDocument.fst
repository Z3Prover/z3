module Z3IndependentGroundDocument

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module D = Z3DefinitionRecognition
module P = Z3DocumentSyntax
module Prep = Z3DocumentPreparation
module U = Z3UnifiedProofSyntax
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module SP = Z3SortedProof
module Root = Z3SortedRootDocument
module Ground = Z3IndependentGroundDefinition
module GroundRoot = Z3IndependentGroundDefinitionRoot
module Cached = Z3IndependentCachedReplay
module RootReplay = Z3IndependentRootReplay

let max_entries : nat = 2000000

let rec bounded_entries (fuel:nat) (entries:list P.entry)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | _ :: rest -> if fuel = 0 then false else bounded_entries (fuel - 1) rest

let within_budget (doc:P.document) : bool =
  bounded_entries max_entries doc.P.entries &&
  Some? (arguments_budget 2000000 doc.P.assertions)

let rec first_definition (entries:list P.entry)
  : Tot (option (e:P.entry{e.P.rule == U.DefinitionIntroduction /\ e.P.premise_ids == []}))
      (decreases entries) =
  match entries with
  | [] -> None
  | entry :: rest ->
    if entry.P.rule = U.DefinitionIntroduction && entry.P.premise_ids = []
    then Some entry else first_definition rest

let choose (schema:S.checked_schema) (doc:P.document) : option (choice schema doc) =
  match first_definition doc.P.entries with
  | None -> None
  | Some entry ->
    (match Ground.recognize schema doc.P.assertions entry.P.formula with
     | None -> None
     | Some d -> Some (entry, d))

let rec rewrite_entries (selected:P.entry) (entries:list P.entry) (acc:list P.entry)
  : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> rev acc
  | entry :: rest ->
    let updated =
      if entry.P.rule = U.DefinitionIntroduction && entry.P.premise_ids = [] &&
         entry.P.formula = selected.P.formula
      then { entry with P.rule = U.Asserted } else entry in
    rewrite_entries selected rest (updated :: acc)

let augment (doc:P.document) (entry:P.entry) : P.document =
  { doc with P.assertions = doc.P.assertions @ [entry.P.formula];
             P.entries = rewrite_entries entry doc.P.entries [] }

let selected (schema:S.schema) (doc:P.document) : option P.document =
  if S.valid schema && within_budget doc then
    match choose schema doc with
    | Some c ->
      let augmented = augment doc (fst c) in
      if Root.check_root_document_epsilon schema augmented = Root.RootCertified
      then Some augmented else None
    | None -> None
  else None

let rec collect_expansion_definitions (defs:list D.definition) (entries:list P.entry)
  : Tot (option (list D.definition)) (decreases entries) =
  match entries with
  | [] -> if defs = [] then None else Some defs
  | entry :: rest ->
    if entry.P.rule <> U.DefinitionIntroduction then
      collect_expansion_definitions defs rest
    else if entry.P.premise_ids <> [] || not (D.scoped [] entry.P.formula) then None
    else
      match D.definition_of entry.P.formula with
      | Some d ->
        if d.D.symbol.domain <> [] || d.D.variables <> [] then None
        else
          (match D.add_definition defs d with
           | Some next -> collect_expansion_definitions next rest
           | None -> None)
      | None -> None

let rec expand_definition_entries (defs:list D.definition) (entries:list P.entry)
  : Tot (option (list P.entry)) (decreases entries) =
  match entries with
  | [] -> Some []
  | entry :: rest ->
    (match D.expand (length defs) defs entry.P.formula,
           (if entry.P.rule = U.DefinitionIntroduction then Some U.DefAxiom
            else Prep.expand_rule_using D.linear_expander defs entry.P.rule),
           expand_definition_entries defs rest with
     | Some formula, Some rule, Some expanded ->
       Some ({ entry with P.formula = formula; P.rule = rule } :: expanded)
     | _, _, _ -> None)

let expand_definitions (doc:P.document) : option P.document =
  match collect_expansion_definitions [] doc.P.entries with
  | Some defs ->
    if D.acyclic (length defs) defs defs && D.fresh_args defs doc.P.assertions then
      (match expand_definition_entries defs doc.P.entries with
       | Some entries -> Some { doc with P.entries = entries }
       | None -> None)
    else None
  | None -> None

let rec entry_formulas (entries:list P.entry) : Tot (list expr) (decreases entries) =
  match entries with
  | [] -> []
  | entry :: rest -> entry.P.formula :: entry_formulas rest

let selected_expanded (schema:S.schema) (doc:P.document) : option P.document =
  let formulas = entry_formulas doc.P.entries in
  if S.valid schema && within_budget doc &&
     Some? (arguments_budget 2000000 formulas) then
    match expand_definitions doc with
    | Some expanded ->
      if Some? (arguments_budget 2000000 (entry_formulas expanded.P.entries)) &&
         Root.check_root_document_epsilon schema expanded = Root.RootCertified
      then Some expanded else None
    | None -> None
  else None

let selected_expanded_cached (schema:S.checked_schema) (doc:P.document)
  (assertions:list expr) (memo:Cached.cache schema assertions) : option P.document =
  let formulas = entry_formulas doc.P.entries in
  if within_budget doc && Some? (arguments_budget 2000000 formulas) then
    match expand_definitions doc with
    | Some expanded ->
      if Some? (arguments_budget 2000000 (entry_formulas expanded.P.entries)) &&
         RootReplay.check_with_cache schema expanded assertions memo = Root.RootCertified
      then Some expanded else None
    | None -> None
  else None

let lemma_selected_expanded_cached (schema:S.checked_schema) (doc:P.document)
  (assertions:list expr) (memo:Cached.cache schema assertions)
  : Lemma (selected_expanded_cached schema doc assertions memo == selected_expanded schema doc) =
  assert (selected_expanded_cached schema doc assertions memo == selected_expanded schema doc)

let lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires Some? (selected schema doc) /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  match choose schema doc with
  | None -> ()
  | Some (entry, d) ->
    let bc = TR.booleans u in
    let eq = SR.root_scalars u in
    let extended = Ground.override schema bc eq model doc.P.assertions entry.P.formula d in
    GroundRoot.lemma_override_root u schema bc eq doc.P.assertions entry.P.formula d model;
    Ground.lemma_inputs schema bc eq model doc.P.assertions entry.P.formula d;
    Ground.lemma_definition schema bc eq model doc.P.assertions entry.P.formula d;
    SP.lemma_truths_append schema bc eq extended doc.P.assertions [entry.P.formula];
    Root.lemma_truths_agreement u schema model doc.P.assertions;
    Root.lemma_truths_agreement u schema extended (augment doc entry).P.assertions;
    Root.lemma_root_certified_epsilon u schema (augment doc entry) extended

let lemma_certified_expanded (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires Some? (selected_expanded schema doc) /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  match expand_definitions doc with
  | None -> ()
  | Some expanded ->
    Root.lemma_root_certified_epsilon u schema expanded model;
    assert (expanded.P.assertions == doc.P.assertions)
