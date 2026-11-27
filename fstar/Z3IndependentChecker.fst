module Z3IndependentChecker

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module A = Z3AstTheory
module Tags = Z3OperatorTags
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module SP = Z3SortedProof
module Replay = Z3IndependentDistinctReplay
module SR = Z3SortedRoot
module K = Z3SortedDistinct
module Skolem = Z3IndependentSkolemRoot
module SkolemModel = Z3IndependentSkolemModel
module DReplay = Z3IndependentDependentReplay
module Binder = Z3IndependentBinderElaboration
module V = Z3DatatypeValue
module FF = Z3SortedFiniteField
module Field = Z3IndependentFiniteFieldDocument
module FieldRoot = Z3IndependentFiniteFieldRoot
module Array = Z3IndependentArrayDocument
module ArrayDefinition = Z3IndependentArrayDefinitionDocument
module ArrayGround = Z3IndependentArrayGroundDocument
module GroundDocument = Z3IndependentGroundDocument
module Definition = Z3IndependentDefinitionDocument
module DefinitionNnf = Z3IndependentDefinitionNnfDocument
module DefinitionSkolem = Z3IndependentDefinitionSkolemDocument
module CertificateFallback = Z3IndependentCertificateFallback
module RootReplay = Z3IndependentRootReplay
module Cached = Z3IndependentCachedReplay

let rec has_array_declarations (declarations:list A.func_decl) : Tot bool
  (decreases declarations) =
  match declarations with
  | [] -> false
  | declaration :: rest ->
    declaration.A.interp = Some Tags.op_select ||
    declaration.A.interp = Some Tags.op_store ||
    has_array_declarations rest

let has_array_symbols (doc:P.document) : bool =
  has_array_declarations doc.P.declarations

let check (schema:S.schema) (doc:P.document) : Root.root_verdict =
  RootReplay.check_recovering schema doc

let diagnose (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  let _, diagnostic = SP.check_document_epsilon_diagnosed schema doc in
  diagnostic

let check_diagnosed (schema:S.schema) (doc:P.document)
  : Root.root_verdict & P.document_diagnostic =
  RootReplay.check_recovering_diagnosed schema doc

let check_distinct (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = check schema doc in
  match base with
  | Root.RootPending _ ->
    if Replay.has_candidates doc &&
       Root.check_root_document_epsilon schema (Replay.augment doc) = Root.RootCertified
    then Root.RootCertified else base
  | _ -> base

let diagnose_distinct (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  match check schema doc with
  | Root.RootPending _ ->
    if Replay.has_candidates doc then
      let augmented = Replay.augment doc in
      if Root.check_root_document_epsilon schema augmented = Root.RootCertified
      then diagnose schema augmented else diagnose schema doc
    else diagnose schema doc
  | _ -> diagnose schema doc

let check_skolem (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = check schema doc in
  match base with
  | Root.RootPending _ ->
    if S.valid schema &&
       (Skolem.check schema doc = Root.RootCertified ||
        (Skolem.contexts_may_differ schema doc &&
         Skolem.check_dependent schema doc = Root.RootCertified) ||
        Skolem.check_binder schema doc = Root.RootCertified)
    then Root.RootCertified else base
  | _ -> base

let diagnose_skolem (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  match check schema doc with
  | Root.RootPending _ ->
    if S.valid schema && Skolem.check schema doc = Root.RootCertified then (
      let expanded = SkolemModel.elaborate schema doc in
      snd (SP.check_document_diagnosed schema expanded))
    else if S.valid schema && Skolem.contexts_may_differ schema doc &&
            Skolem.check_dependent schema doc = Root.RootCertified then (
      let expanded = SkolemModel.elaborate_dependent schema doc in
      snd (SP.check_document_diagnosed schema expanded))
    else if S.valid schema && Skolem.check_binder schema doc = Root.RootCertified then (
      let expanded = SkolemModel.elaborate_binder schema doc in
      snd (SP.check_document_diagnosed schema expanded))
    else diagnose schema doc
  | _ -> diagnose schema doc

let field_augmented (schema:S.schema) (doc:P.document) : option P.document =
  match Field.modulus doc with
  | Some p ->
    if p > 1 && S.valid schema && not (V.datatype_sort (S.signature schema) (FF.ff_sort p)) &&
       Field.has_candidates p doc then
      let augmented = Field.augment p doc in
      if Root.check_root_document_epsilon schema augmented = Root.RootCertified
      then Some augmented else None
    else None
  | None -> None

let check_field (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = check schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (field_augmented schema doc) then Root.RootCertified else base
  | _ -> base

let diagnose_field (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  match check schema doc with
  | Root.RootPending _ ->
    (match field_augmented schema doc with
     | Some augmented -> diagnose schema augmented
     | None -> diagnose schema doc)
  | _ -> diagnose schema doc

let field_augmented_with_evidence (schema:S.schema) (doc:P.document)
  (evidence:option (int & list int)) : option P.document =
  match Field.modulus doc with
  | Some p ->
    if p > 1 && S.valid schema && not (V.datatype_sort (S.signature schema) (FF.ff_sort p)) &&
       Field.has_candidates_with_evidence p doc evidence then
      let augmented = Field.augment_with_evidence p doc evidence in
      if Root.check_root_document_epsilon schema augmented = Root.RootCertified
      then Some augmented else None
    else None
  | None -> None

let check_field_with_evidence (schema:S.schema) (doc:P.document)
  (evidence:option (int & list int)) : Root.root_verdict =
  let base = check schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (field_augmented_with_evidence schema doc evidence) then Root.RootCertified else base
  | _ -> base

let diagnose_field_with_evidence (schema:S.schema) (doc:P.document)
  (evidence:option (int & list int)) : P.document_diagnostic =
  match check schema doc with
  | Root.RootPending _ ->
    (match field_augmented_with_evidence schema doc evidence with
     | Some augmented -> diagnose schema augmented
     | None -> diagnose schema doc)
  | _ -> diagnose schema doc

let check_array (schema:S.schema) (doc:P.document) : Root.root_verdict =
  CertificateFallback.recover schema doc (ArrayDefinition.check schema doc)

let check_array_diagnosed (schema:S.schema) (doc:P.document)
  : Root.root_verdict & P.document_diagnostic =
  let verdict = check_array schema doc in
  verdict, (if verdict = Root.RootCertified then P.DocumentChecked 0 []
            else diagnose schema doc)

let diagnose_array (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  snd (check_array_diagnosed schema doc)

let check_root_document_cached (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{result == Root.check_root_document schema doc} =
  if S.valid schema then
    match Cached.check_document schema doc with
    | None -> Root.RootRejected
    | Some n ->
      if n > 0 then Root.RootPending n
      else if Root.root_covered schema doc then Root.RootCertified
      else Root.RootUncovered
  else Root.RootRejected

let definition_augmented_prepared (schema:S.checked_schema) (doc:P.document)
  : result:option P.document{
      result == (if Definition.eligible schema doc then
                   if Root.check_root_document schema (Definition.augment schema doc) == Root.RootCertified
                   then Some (Definition.augment schema doc)
                   else if Root.check_root_document schema (DefinitionNnf.augment schema doc) == Root.RootCertified
                   then Some (DefinitionNnf.augment schema doc)
                   else None
                 else None)} =
  let items, prepared = Definition.prepare schema doc in
  if Definition.eligible_context schema doc items then
    let augmented = Definition.augment_prepared schema doc items prepared in
    if check_root_document_cached schema augmented = Root.RootCertified
    then Some augmented
    else
      let nnf_augmented = DefinitionNnf.augment_prepared schema doc items augmented in
      if check_root_document_cached schema nnf_augmented = Root.RootCertified
      then Some nnf_augmented else None
  else None

let definition_augmented (schema:S.schema) (doc:P.document) : option P.document =
  if S.valid schema && Definition.has_definition doc.P.entries
  then definition_augmented_prepared schema doc
  else None

let combined_augmented (schema:S.schema) (doc:P.document) : option P.document =
  if S.valid schema && skolem_with_definitions doc.P.entries false false &&
     DefinitionSkolem.eligible schema doc then
    let augmented = DefinitionSkolem.augment schema doc in
    if check_root_document_cached schema augmented = Root.RootCertified
    then Some augmented else None
  else None

let combined_dependent_augmented (schema:S.schema) (doc:P.document) : option P.document =
  if S.valid schema && has_definition doc.P.entries && DReplay.may_change schema doc &&
     DefinitionSkolem.eligible_dependent schema doc then
    let augmented = DefinitionSkolem.augment_dependent schema doc in
    if check_root_document_cached schema augmented = Root.RootCertified
    then Some augmented else None
  else None

let combined_binder_augmented (schema:S.schema) (doc:P.document) : option P.document =
  if S.valid schema && has_definition doc.P.entries &&
     DefinitionSkolem.eligible_dependent schema doc then
    let prepared = DefinitionSkolem.augment_dependent schema doc in
    let augmented, selected = Binder.augment_with_selection schema prepared in
    if selected <> [] && check_root_document_cached schema augmented = Root.RootCertified
    then Some augmented else None
  else None

let check_definition_from_using (schema:S.schema) (doc:P.document)
                                (base:Root.root_verdict)
                                (expanded:unit -> option P.document) : Root.root_verdict =
  match base with
  | Root.RootPending _ ->
    if Some? (definition_augmented schema doc) ||
       Some? (combined_augmented schema doc) ||
       Some? (combined_dependent_augmented schema doc) ||
       Some? (combined_binder_augmented schema doc) ||
       (not (has_definition doc.P.entries) && S.valid schema &&
        (if DReplay.may_change schema doc then
           Skolem.check_dependent schema doc = Root.RootCertified ||
           Skolem.check_binder_selected schema doc
         else has_quant_intro doc.P.entries && Skolem.check_binder_selected schema doc)) ||
       (skolem_without_definitions doc.P.entries false &&
        S.valid schema && Skolem.check schema doc = Root.RootCertified) ||
       (has_definition doc.P.entries &&
        (Some? (GroundDocument.selected schema doc) ||
         Some? (expanded ())))
    then Root.RootCertified else base
  | _ -> base

let check_definition_from (schema:S.schema) (doc:P.document)
                          (base:Root.root_verdict) : Root.root_verdict =
  check_definition_from_using schema doc base
    (fun _ -> GroundDocument.selected_expanded schema doc)

let check_definition_from_cached (schema:S.checked_schema) (doc:P.document)
  (base:Root.root_verdict) (assertions:list Z3AstTheory.expr)
  (memo:Cached.cache schema assertions)
  : result:Root.root_verdict{result == check_definition_from schema doc base} =
  let verdict =
    check_definition_from_using schema doc base
      (fun _ -> GroundDocument.selected_expanded_cached schema doc assertions memo) in
  GroundDocument.lemma_selected_expanded_cached schema doc assertions memo;
  verdict

let check_definition (schema:S.schema) (doc:P.document) : Root.root_verdict =
  if S.valid schema && has_definition doc.P.entries then
    let checked = schema in
    let base, (_, memo) = RootReplay.check_recovering_diagnosed_cached checked doc in
    check_definition_from_cached checked doc base (SP.elaborate_full checked doc).P.assertions memo
  else check_definition_from schema doc (check schema doc)

let check_definition_diagnosed (schema:S.schema) (doc:P.document)
  : Root.root_verdict & P.document_diagnostic =
  if S.valid schema && has_definition doc.P.entries then
    let checked = schema in
    let base, (diagnostic, memo) =
      RootReplay.check_recovering_diagnosed_cached checked doc in
    let verdict =
      check_definition_from_cached checked doc base (SP.elaborate_full checked doc).P.assertions memo in
    verdict, (if verdict = Root.RootCertified then P.DocumentChecked 0 [] else diagnostic)
  else
    let base, diagnostic = check_diagnosed schema doc in
    let verdict = check_definition_from schema doc base in
    verdict, (if verdict = Root.RootCertified then P.DocumentChecked 0 [] else diagnostic)

let array_extension_from (schema:S.schema) (doc:P.document)
                         (base:Root.root_verdict) : Root.root_verdict =
  match base with
  | Root.RootPending _ ->
    if Some? (Array.selected schema doc) ||
       Some? (ArrayDefinition.selected schema doc) ||
       (Definition.has_definition doc.P.entries && Some? (ArrayGround.selected schema doc))
    then Root.RootCertified else base
  | _ -> base

let check_array_from (schema:S.schema) (doc:P.document)
  (base:Root.root_verdict{base == check schema doc})
  : result:Root.root_verdict{result == check_array schema doc} =
  array_extension_from schema doc base

let check_definition_array_from (schema:S.schema) (doc:P.document)
                                (base:Root.root_verdict) : Root.root_verdict =
  array_extension_from schema doc base

let check_definition_array (schema:S.schema) (doc:P.document) : Root.root_verdict =
  check_definition_array_from schema doc (check_definition schema doc)

let check_definition_array_fast (schema:S.schema) (doc:P.document) : Root.root_verdict =
  if not (Definition.has_definition doc.P.entries) &&
     has_array_symbols doc && Array.has_candidates schema doc then
    match Array.selected schema doc with
    | Some _ -> Root.RootCertified
    | None -> check_definition_array schema doc
  else check_definition_array schema doc

let check_definition_array_diagnosed (schema:S.schema) (doc:P.document)
  : Root.root_verdict & P.document_diagnostic =
  let base, diagnostic = check_definition_diagnosed schema doc in
  let verdict = check_definition_array_from schema doc base in
  verdict, (if verdict = Root.RootCertified then P.DocumentChecked 0 [] else diagnostic)

let check_definition_array_fast_diagnosed (schema:S.schema) (doc:P.document)
  : Root.root_verdict & P.document_diagnostic =
  let verdict = check_definition_array_fast schema doc in
  verdict, (if verdict = Root.RootCertified then P.DocumentChecked 0 []
            else diagnose schema doc)

let diagnose_definition (schema:S.schema) (doc:P.document) : P.document_diagnostic =
  match check schema doc with
  | Root.RootPending _ ->
    (match definition_augmented schema doc with
     | Some augmented -> snd (SP.check_document_diagnosed schema augmented)
     | None ->
       (match combined_augmented schema doc with
        | Some augmented -> snd (SP.check_document_diagnosed schema augmented)
        | None ->
          (match combined_dependent_augmented schema doc with
           | Some augmented -> snd (SP.check_document_diagnosed schema augmented)
           | None ->
             (match combined_binder_augmented schema doc with
              | Some augmented -> snd (SP.check_document_diagnosed schema augmented)
              | None ->
                if skolem_without_definitions doc.P.entries false &&
                   S.valid schema && Skolem.check schema doc = Root.RootCertified
                then snd (SP.check_document_diagnosed schema (SkolemModel.elaborate schema doc))
                else if not (has_definition doc.P.entries) && S.valid schema then
                  if DReplay.may_change schema doc then
                    if Skolem.check_dependent schema doc = Root.RootCertified
                    then snd (SP.check_document_diagnosed schema (SkolemModel.elaborate_dependent schema doc))
                    else if Skolem.check_binder_selected schema doc
                    then snd (SP.check_document_diagnosed schema (SkolemModel.elaborate_binder schema doc))
                    else diagnose schema doc
                  else if has_quant_intro doc.P.entries && Skolem.check_binder_selected schema doc
                  then snd (SP.check_document_diagnosed schema (SkolemModel.elaborate_binder schema doc))
                  else diagnose schema doc
                else
                  (match GroundDocument.selected schema doc with
                   | Some augmented -> diagnose schema augmented
                   | None ->
                     (match GroundDocument.selected_expanded schema doc with
                      | Some augmented -> diagnose schema augmented
                      | None -> diagnose schema doc))))))
  | _ -> diagnose schema doc

let lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
                    (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  CertificateFallback.lemma_certified u schema doc (Root.check_root_document_epsilon schema doc) model

let lemma_certified_distinct (u:TR.uninterpreted) (schema:S.checked_schema)
                             (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_distinct schema doc == Root.RootCertified /\
                    TR.root_model u schema model /\
                    K.model schema (TR.booleans u) (SR.root_scalars u) model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  match check schema doc with
  | Root.RootPending _ -> Replay.lemma_certified u schema doc model
  | _ -> lemma_certified u schema doc model

let lemma_certified_skolem (u:TR.uninterpreted) (schema:S.checked_schema)
                           (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_skolem schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  match check schema doc with
  | Root.RootPending _ ->
    if Skolem.check schema doc = Root.RootCertified then
      Skolem.lemma_certified u schema doc model
    else if Skolem.contexts_may_differ schema doc &&
            Skolem.check_dependent schema doc = Root.RootCertified then
      Skolem.lemma_certified_dependent u schema doc model
    else Skolem.lemma_certified_binder u schema doc model
  | _ -> lemma_certified u schema doc model

let lemma_certified_field (u:TR.uninterpreted) (schema:S.checked_schema)
                          (doc:P.document)
                          (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
                          (symbols:TR.symbols u schema)
  : Lemma (requires check_field schema doc == Root.RootCertified /\ Field.modulus doc == Some p)
          (ensures not (Root.root_truths u schema
            (TR.standard u schema (FieldRoot.field_symbols u schema p symbols)) doc.P.assertions)) =
  let root = TR.standard u schema (FieldRoot.field_symbols u schema p symbols) in
  match check schema doc with
  | Root.RootPending _ -> Field.lemma_certified u schema p doc symbols
  | _ ->
    FieldRoot.lemma_root_inhabited u schema p symbols;
    lemma_certified u schema doc root

let lemma_certified_field_with_evidence (u:TR.uninterpreted) (schema:S.checked_schema)
                          (doc:P.document)
                          (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
                          (symbols:TR.symbols u schema) (evidence:option (int & list int))
  : Lemma (requires check_field_with_evidence schema doc evidence == Root.RootCertified /\
                    Field.modulus doc == Some p)
          (ensures not (Root.root_truths u schema
            (TR.standard u schema (FieldRoot.field_symbols u schema p symbols)) doc.P.assertions)) =
  let root = TR.standard u schema (FieldRoot.field_symbols u schema p symbols) in
  match check schema doc with
  | Root.RootPending _ -> Field.lemma_certified_with_evidence u schema p doc symbols evidence
  | _ ->
    FieldRoot.lemma_root_inhabited u schema p symbols;
    lemma_certified u schema doc root

let lemma_certified_array (u:TR.uninterpreted) (schema:S.checked_schema)
                          (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires check_array schema doc == Root.RootCertified)
          (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions)) =
  match check schema doc with
  | Root.RootPending _ -> ArrayDefinition.lemma_certified u schema doc symbols
  | _ ->
    TR.lemma_standard_root u schema symbols;
    lemma_certified u schema doc (TR.standard u schema symbols)

let lemma_certified_definition (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_definition schema doc == Root.RootCertified /\ TR.root_model u schema model)
    (ensures not (Root.root_truths u schema model doc.P.assertions)) =
  match check schema doc with
  | Root.RootPending _ ->
    if Some? (definition_augmented schema doc) then
      if Root.check_root_document schema (Definition.augment schema doc) = Root.RootCertified then
        Definition.lemma_certified u schema doc model
      else DefinitionNnf.lemma_certified u schema doc model
    else if Some? (combined_augmented schema doc) then
      DefinitionSkolem.lemma_certified u schema doc model
    else if Some? (combined_dependent_augmented schema doc) then
      DefinitionSkolem.lemma_certified_dependent u schema doc model
    else if Some? (combined_binder_augmented schema doc) then
      DefinitionSkolem.lemma_certified_binder u schema doc model
    else if skolem_without_definitions doc.P.entries false &&
            Skolem.check schema doc = Root.RootCertified then
      Skolem.lemma_certified u schema doc model
    else if not (has_definition doc.P.entries) && DReplay.may_change schema doc &&
            Skolem.check_dependent schema doc = Root.RootCertified then
      Skolem.lemma_certified_dependent u schema doc model
    else if has_definition doc.P.entries && Some? (GroundDocument.selected schema doc) then
      GroundDocument.lemma_certified u schema doc model
    else if has_definition doc.P.entries && Some? (GroundDocument.selected_expanded schema doc) then
      GroundDocument.lemma_certified_expanded u schema doc model
    else Skolem.lemma_certified_binder_selected u schema doc model
  | _ -> lemma_certified u schema doc model

let lemma_certified_definition_array (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires check_definition_array schema doc == Root.RootCertified)
    (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions)) =
  match check_definition schema doc with
  | Root.RootPending _ -> lemma_certified_array u schema doc symbols
  | _ ->
    TR.lemma_standard_root u schema symbols;
    lemma_certified_definition u schema doc (TR.standard u schema symbols)

let lemma_certified_definition_array_fast (u:TR.uninterpreted)
  (schema:S.checked_schema) (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires check_definition_array_fast schema doc == Root.RootCertified)
    (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions)) =
  if not (Definition.has_definition doc.P.entries) &&
     has_array_symbols doc && Array.has_candidates schema doc then
    match Array.selected schema doc with
    | Some _ -> Array.lemma_selected_certified u schema doc symbols
    | None -> lemma_certified_definition_array u schema doc symbols
  else lemma_certified_definition_array u schema doc symbols
