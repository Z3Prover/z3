module Z3IndependentSkolemRoot

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot

val check (schema:S.schema) (doc:P.document) : Root.root_verdict
val check_dependent (schema:S.schema) (doc:P.document) : Root.root_verdict
val check_binder (schema:S.schema) (doc:P.document) : Root.root_verdict
val check_binder_selected (schema:S.schema) (doc:P.document) : bool
val contexts_may_differ (schema:S.schema) (doc:P.document) : bool

val lemma_same_context_verdict (schema:S.checked_schema) (doc:P.document)
  : Lemma (requires not (contexts_may_differ schema doc))
          (ensures check_dependent schema doc == check schema doc)

val lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))

val lemma_certified_dependent (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_dependent schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))

val lemma_certified_binder (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_binder schema doc == Root.RootCertified /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))

val lemma_certified_binder_selected (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires check_binder_selected schema doc /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))
