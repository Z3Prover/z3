module Z3IndependentDefinitionSkolemDocument

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module Binder = Z3IndependentBinderElaboration

val eligible (s:S.checked_schema) (doc:P.document) : bool
val augment (s:S.checked_schema) (doc:P.document) : P.document

val lemma_certified (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires eligible s doc /\
      Root.check_root_document s (augment s doc) == Root.RootCertified /\
      TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions))

val eligible_dependent (s:S.checked_schema) (doc:P.document) : bool
val augment_dependent (s:S.checked_schema) (doc:P.document) : P.document

val lemma_certified_dependent (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires eligible_dependent s doc /\
      Root.check_root_document s (augment_dependent s doc) == Root.RootCertified /\
      TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions))

val augment_binder (s:S.checked_schema) (doc:P.document)
  : result:P.document{result == Binder.augment s (augment_dependent s doc)}

val lemma_certified_binder (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires eligible_dependent s doc /\
      Root.check_root_document s (augment_binder s doc) == Root.RootCertified /\
      TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions))
