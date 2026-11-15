module Z3IndependentArrayDefinitionDocument

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module TR = Z3TypedRoot
module Root = Z3SortedRootDocument
module Array = Z3IndependentArrayDocument
module AP = Z3IndependentArrayPreservation
module AI = Z3IndependentArrayInterpretation
module Definition = Z3IndependentDefinitionDocument
module ArrayGround = Z3IndependentArrayGroundDocument

let selected (schema:S.schema) (doc:P.document) : option P.document =
  if S.valid schema && Definition.has_definition doc.P.entries &&
     Array.within_budget doc &&
     AP.eligible (S.signature schema) Array.max_assertions doc.P.assertions &&
     Array.has_candidates schema doc then
    let array_doc = Array.augment schema doc in
    if Definition.eligible schema array_doc then
      let augmented = Definition.augment schema array_doc in
      if Root.check_root_document schema augmented = Root.RootCertified
      then Some augmented else None
    else None
  else None

let check (schema:S.schema) (doc:P.document) : Root.root_verdict =
  let base = Array.check schema doc in
  match base with
  | Root.RootPending _ ->
    if Some? (selected schema doc) ||
       (Definition.has_definition doc.P.entries && Some? (ArrayGround.selected schema doc))
    then Root.RootCertified else base
  | _ -> base

let lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
                    (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires check schema doc == Root.RootCertified)
          (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions)) =
  match Array.check schema doc with
  | Root.RootPending _ ->
    if Some? (selected schema doc) then
      let array_doc = Array.augment schema doc in
      let extended = TR.standard u schema (AI.symbols u schema symbols) in
      AI.lemma_root_inhabited u schema symbols;
      Array.lemma_augment_truths u schema doc symbols;
      Definition.lemma_certified u schema array_doc extended
    else ArrayGround.lemma_certified u schema doc symbols
  | _ -> Array.lemma_certified u schema doc symbols
