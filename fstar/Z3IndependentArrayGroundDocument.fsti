module Z3IndependentArrayGroundDocument

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module TR = Z3TypedRoot
module Root = Z3SortedRootDocument
module Array = Z3IndependentArrayDocument
module AP = Z3IndependentArrayPreservation
module Ground = Z3IndependentGroundDocument

val selected (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (if S.valid schema && Ground.within_budget doc then
                   match Ground.choose schema doc with
                   | Some c ->
                     if Array.within_budget doc &&
                        AP.eligible (S.signature schema) Array.max_assertions doc.P.assertions &&
                        Array.has_candidates schema doc then
                       let augmented = Array.augment schema (Ground.augment doc (fst c)) in
                       if Root.check_root_document_epsilon schema augmented == Root.RootCertified
                       then Some augmented else None
                     else None
                   | None -> None
                 else None)}

val lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires Some? (selected schema doc))
          (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions))
