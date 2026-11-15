module Z3IndependentArrayDefinitionDocument

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module TR = Z3TypedRoot
module Root = Z3SortedRootDocument
module Array = Z3IndependentArrayDocument
module AP = Z3IndependentArrayPreservation
module Definition = Z3IndependentDefinitionDocument
module ArrayGround = Z3IndependentArrayGroundDocument

val selected (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (if S.valid schema && Definition.has_definition doc.P.entries &&
                    Array.within_budget doc &&
                    AP.eligible (S.signature schema) Array.max_assertions doc.P.assertions &&
                    Array.has_candidates schema doc then
                   let array_doc = Array.augment schema doc in
                   if Definition.eligible schema array_doc &&
                      Root.check_root_document schema (Definition.augment schema array_doc) == Root.RootCertified
                   then Some (Definition.augment schema array_doc) else None
                 else None)}

val check (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == (match Array.check schema doc with
        | Root.RootPending _ ->
          if Some? (selected schema doc) ||
             (Definition.has_definition doc.P.entries && Some? (ArrayGround.selected schema doc))
          then Root.RootCertified else Array.check schema doc
        | verdict -> verdict)}

val lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires check schema doc == Root.RootCertified)
          (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions))
