module Z3IndependentChecker

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
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
module RootReplay = Z3IndependentRootReplay
module Cached = Z3IndependentCachedReplay
module Definition = Z3IndependentDefinitionDocument
module DefinitionNnf = Z3IndependentDefinitionNnfDocument
module DefinitionSkolem = Z3IndependentDefinitionSkolemDocument
module U = Z3UnifiedProofSyntax
module NR = Z3NnfReplay
module CertificateFallback = Z3IndependentCertificateFallback

val check (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == CertificateFallback.recover schema doc (Root.check_root_document_epsilon schema doc)}

val diagnose (schema:S.schema) (doc:P.document)
  : result:P.document_diagnostic{
      SP.diagnostic_result result == SP.check_document_epsilon schema doc}

val check_diagnosed (schema:S.schema) (doc:P.document)
  : result:(Root.root_verdict & P.document_diagnostic){
      fst result == check schema doc /\
      snd result == diagnose schema doc}

val check_distinct (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == (match check schema doc with
        | Root.RootPending _ ->
          if Replay.has_candidates doc &&
             Root.check_root_document_epsilon schema (Replay.augment doc) == Root.RootCertified
          then Root.RootCertified else check schema doc
        | verdict -> verdict)}

val diagnose_distinct (schema:S.schema) (doc:P.document)
  : result:P.document_diagnostic{
      SP.diagnostic_result result ==
        (match check schema doc with
         | Root.RootPending _ ->
           if Replay.has_candidates doc &&
              Root.check_root_document_epsilon schema (Replay.augment doc) == Root.RootCertified
           then SP.check_document_epsilon schema (Replay.augment doc)
           else SP.check_document_epsilon schema doc
         | _ -> SP.check_document_epsilon schema doc)}

val check_skolem (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == (match check schema doc with
        | Root.RootPending _ ->
          if S.valid schema &&
             (Skolem.check schema doc == Root.RootCertified \/
              (Skolem.contexts_may_differ schema doc /\
               Skolem.check_dependent schema doc == Root.RootCertified) \/
              Skolem.check_binder schema doc == Root.RootCertified)
          then Root.RootCertified else check schema doc
        | verdict -> verdict)}

val diagnose_skolem (schema:S.schema) (doc:P.document)
  : result:P.document_diagnostic{
      SP.diagnostic_result result ==
        (match check schema doc with
         | Root.RootPending _ ->
           if S.valid schema && Skolem.check schema doc == Root.RootCertified
           then SP.check_document schema (SkolemModel.elaborate schema doc)
           else if S.valid schema && Skolem.contexts_may_differ schema doc &&
                   Skolem.check_dependent schema doc == Root.RootCertified
           then SP.check_document schema (SkolemModel.elaborate_dependent schema doc)
           else if S.valid schema && Skolem.check_binder schema doc == Root.RootCertified
           then SP.check_document schema (SkolemModel.elaborate_binder schema doc)
           else SP.check_document_epsilon schema doc
         | _ -> SP.check_document_epsilon schema doc)}

val field_augmented (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (match Field.modulus doc with
        | Some p ->
          if p > 1 && S.valid schema &&
             not (V.datatype_sort (S.signature schema) (FF.ff_sort p)) &&
             Field.has_candidates p doc &&
             Root.check_root_document_epsilon schema (Field.augment p doc) == Root.RootCertified
          then Some (Field.augment p doc) else None
        | None -> None)}
val check_field (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == (match check schema doc with
        | Root.RootPending _ ->
          if Some? (field_augmented schema doc) then Root.RootCertified else check schema doc
        | verdict -> verdict)}
val diagnose_field (schema:S.schema) (doc:P.document)
  : result:P.document_diagnostic{
      SP.diagnostic_result result ==
        (match check schema doc with
         | Root.RootPending _ ->
           (match field_augmented schema doc with
            | Some augmented -> SP.check_document_epsilon schema augmented
            | None -> SP.check_document_epsilon schema doc)
         | _ -> SP.check_document_epsilon schema doc)}

val field_augmented_with_evidence (schema:S.schema) (doc:P.document)
  (evidence:option (int & list int))
  : result:option P.document{
      result == (match Field.modulus doc with
        | Some p ->
          if p > 1 && S.valid schema &&
             not (V.datatype_sort (S.signature schema) (FF.ff_sort p)) &&
             Field.has_candidates_with_evidence p doc evidence &&
             Root.check_root_document_epsilon schema (Field.augment_with_evidence p doc evidence) == Root.RootCertified
          then Some (Field.augment_with_evidence p doc evidence) else None
        | None -> None)}
val check_field_with_evidence (schema:S.schema) (doc:P.document)
  (evidence:option (int & list int))
  : result:Root.root_verdict{
      result == (match check schema doc with
        | Root.RootPending _ ->
          if Some? (field_augmented_with_evidence schema doc evidence)
          then Root.RootCertified else check schema doc
        | verdict -> verdict)}
val diagnose_field_with_evidence (schema:S.schema) (doc:P.document)
  (evidence:option (int & list int))
  : result:P.document_diagnostic{
      SP.diagnostic_result result ==
        (match check schema doc with
         | Root.RootPending _ ->
           (match field_augmented_with_evidence schema doc evidence with
            | Some augmented -> SP.check_document_epsilon schema augmented
            | None -> SP.check_document_epsilon schema doc)
         | _ -> SP.check_document_epsilon schema doc)}

val check_array (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == (match check schema doc with
        | Root.RootPending _ -> ArrayDefinition.check schema doc
        | verdict -> verdict)}
val check_array_diagnosed (schema:S.schema) (doc:P.document)
  : result:(Root.root_verdict & P.document_diagnostic){
      fst result == check_array schema doc /\
      snd result == (if fst result == Root.RootCertified
                     then P.DocumentChecked 0 []
                     else diagnose schema doc)}
val diagnose_array (schema:S.schema) (doc:P.document)
  : result:P.document_diagnostic{
      result == snd (check_array_diagnosed schema doc)}

val definition_augmented (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (if S.valid schema && Definition.has_definition doc.P.entries &&
                    Definition.eligible schema doc then
                   if Root.check_root_document schema (Definition.augment schema doc) == Root.RootCertified
                   then Some (Definition.augment schema doc)
                   else if Root.check_root_document schema (DefinitionNnf.augment schema doc) == Root.RootCertified
                   then Some (DefinitionNnf.augment schema doc)
                   else None
                 else None)}

let rec skolem_without_definitions (entries:list P.entry) (found:bool)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> found
  | e :: rest ->
    if e.P.rule = U.DefinitionIntroduction then false
    else skolem_without_definitions rest (found || e.P.rule = U.Skolemization)

let rec skolem_with_definitions (entries:list P.entry) (definition:bool) (skolem:bool)
  : Tot bool (decreases entries) =
  if definition && skolem then true
  else match entries with
  | [] -> false
  | e :: rest ->
    skolem_with_definitions rest (definition || e.P.rule = U.DefinitionIntroduction)
      (skolem || e.P.rule = U.Skolemization)

let has_definition (entries:list P.entry) : bool = Definition.has_definition entries

let rec has_quant_intro (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest ->
    (match e.P.rule with
     | U.QuantifierIntroduction c -> NR.quant_intro_root c || has_quant_intro rest
     | _ -> has_quant_intro rest)

val combined_augmented (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (if S.valid schema &&
                    skolem_with_definitions doc.P.entries false false &&
                    DefinitionSkolem.eligible schema doc &&
                    Root.check_root_document schema (DefinitionSkolem.augment schema doc) == Root.RootCertified
                 then Some (DefinitionSkolem.augment schema doc) else None)}

val combined_dependent_augmented (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (if S.valid schema && has_definition doc.P.entries &&
                    DReplay.may_change schema doc &&
                    DefinitionSkolem.eligible_dependent schema doc &&
                    Root.check_root_document schema (DefinitionSkolem.augment_dependent schema doc) ==
                      Root.RootCertified
                 then Some (DefinitionSkolem.augment_dependent schema doc) else None)}

val combined_binder_augmented (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (if S.valid schema && has_definition doc.P.entries &&
                    DefinitionSkolem.eligible_dependent schema doc &&
                    snd (Binder.augment_with_selection schema
                      (DefinitionSkolem.augment_dependent schema doc)) <> [] &&
                    Root.check_root_document schema (DefinitionSkolem.augment_binder schema doc) ==
                      Root.RootCertified
                 then Some (DefinitionSkolem.augment_binder schema doc) else None)}

(* Reference order; the implementation may short-circuit binder replay first. *)
val check_definition (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == (match check schema doc with
        | Root.RootPending _ ->
          if Some? (definition_augmented schema doc) ||
             Some? (combined_augmented schema doc) ||
             Some? (combined_dependent_augmented schema doc) ||
             Some? (combined_binder_augmented schema doc) ||
             (skolem_without_definitions doc.P.entries false &&
              S.valid schema && Skolem.check schema doc == Root.RootCertified) ||
             (not (has_definition doc.P.entries) && S.valid schema &&
              (if DReplay.may_change schema doc then
                 Skolem.check_dependent schema doc == Root.RootCertified ||
                 Skolem.check_binder_selected schema doc
               else has_quant_intro doc.P.entries && Skolem.check_binder_selected schema doc)) ||
             (has_definition doc.P.entries &&
              (Some? (GroundDocument.selected schema doc) ||
               Some? (GroundDocument.selected_expanded schema doc)))
          then Root.RootCertified else check schema doc
        | verdict -> verdict)}
val check_definition_diagnosed (schema:S.schema) (doc:P.document)
  : result:(Root.root_verdict & P.document_diagnostic){
      fst result == check_definition schema doc /\
      snd result == (if fst result == Root.RootCertified
                     then P.DocumentChecked 0 []
                     else diagnose schema doc)}
val check_definition_array (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == (match check_definition schema doc with
        | Root.RootPending _ ->
          if check_array schema doc == Root.RootCertified
          then Root.RootCertified else check_definition schema doc
        | verdict -> verdict)}
val check_definition_array_diagnosed (schema:S.schema) (doc:P.document)
  : result:(Root.root_verdict & P.document_diagnostic){
      fst result == check_definition_array schema doc /\
      snd result == (if fst result == Root.RootCertified
                     then P.DocumentChecked 0 []
                     else diagnose schema doc)}
val diagnose_definition (schema:S.schema) (doc:P.document)
  : result:P.document_diagnostic{
      SP.diagnostic_result result ==
        (match check schema doc with
         | Root.RootPending _ ->
           (match definition_augmented schema doc with
            | Some augmented -> SP.check_document schema augmented
            | None ->
              (match combined_augmented schema doc with
               | Some augmented -> SP.check_document schema augmented
               | None ->
                 (match combined_dependent_augmented schema doc with
                  | Some augmented -> SP.check_document schema augmented
                  | None ->
                    (match combined_binder_augmented schema doc with
                     | Some augmented -> SP.check_document schema augmented
                     | None ->
                       if skolem_without_definitions doc.P.entries false &&
                          S.valid schema && Skolem.check schema doc == Root.RootCertified
                       then SP.check_document schema (SkolemModel.elaborate schema doc)
                       else if not (has_definition doc.P.entries) && S.valid schema then
                         if DReplay.may_change schema doc then
                           if Skolem.check_dependent schema doc == Root.RootCertified
                           then SP.check_document schema (SkolemModel.elaborate_dependent schema doc)
                           else if Skolem.check_binder_selected schema doc
                           then SP.check_document schema (SkolemModel.elaborate_binder schema doc)
                           else SP.check_document_epsilon schema doc
                         else if has_quant_intro doc.P.entries && Skolem.check_binder_selected schema doc
                         then SP.check_document schema (SkolemModel.elaborate_binder schema doc)
                         else SP.check_document_epsilon schema doc
                       else
                         (match GroundDocument.selected schema doc with
                          | Some augmented -> SP.check_document_epsilon schema augmented
                          | None ->
                            (match GroundDocument.selected_expanded schema doc with
                             | Some augmented -> SP.check_document_epsilon schema augmented
                             | None -> SP.check_document_epsilon schema doc))))))
         | _ -> SP.check_document_epsilon schema doc)}

val lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
                    (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))

val lemma_certified_distinct (u:TR.uninterpreted) (schema:S.checked_schema)
                             (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_distinct schema doc == Root.RootCertified /\
                    TR.root_model u schema model /\
                    K.model schema (TR.booleans u) (SR.root_scalars u) model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))

val lemma_certified_skolem (u:TR.uninterpreted) (schema:S.checked_schema)
                           (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_skolem schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))

val lemma_certified_field (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
  (symbols:TR.symbols u schema)
  : Lemma (requires check_field schema doc == Root.RootCertified /\ Field.modulus doc == Some p)
          (ensures not (Root.root_truths u schema
            (TR.standard u schema (FieldRoot.field_symbols u schema p symbols)) doc.P.assertions))

val lemma_certified_field_with_evidence (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
  (symbols:TR.symbols u schema) (evidence:option (int & list int))
  : Lemma (requires check_field_with_evidence schema doc evidence == Root.RootCertified /\
                    Field.modulus doc == Some p)
          (ensures not (Root.root_truths u schema
            (TR.standard u schema (FieldRoot.field_symbols u schema p symbols)) doc.P.assertions))

val lemma_certified_array (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires check_array schema doc == Root.RootCertified)
          (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions))

val lemma_certified_definition (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_definition schema doc == Root.RootCertified /\ TR.root_model u schema model)
    (ensures not (Root.root_truths u schema model doc.P.assertions))

val lemma_certified_definition_array (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires check_definition_array schema doc == Root.RootCertified)
    (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions))
