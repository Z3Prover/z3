module Z3IndependentDistinctReplay

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module K = Z3SortedDistinct

val has_candidates (doc:P.document) : bool
val augment (doc:P.document) : P.document

val lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires Root.check_root_document_epsilon schema (augment doc) == Root.RootCertified /\
                    TR.root_model u schema model /\
                    K.model schema (TR.booleans u) (SR.root_scalars u) model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))
