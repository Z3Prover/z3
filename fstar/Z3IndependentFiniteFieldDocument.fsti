module Z3IndependentFiniteFieldDocument

module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module FF = Z3SortedFiniteField
module FR = Z3IndependentFiniteFieldRoot

val has_candidates (p:int) (doc:P.document) : bool
val modulus (doc:P.document) : option int
val augment (p:int) (doc:P.document) : P.document
val has_candidates_with_evidence (p:int) (doc:P.document)
  (evidence:option (int & list int)) : bool
val augment_with_evidence (p:int) (doc:P.document)
  (evidence:option (int & list int)) : P.document

val lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
  (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires Root.check_root_document_epsilon schema (augment p doc) == Root.RootCertified)
          (ensures not (Root.root_truths u schema
            (TR.standard u schema (FR.field_symbols u schema p symbols)) doc.P.assertions))

val lemma_certified_with_evidence (u:TR.uninterpreted) (schema:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature schema) (FF.ff_sort p))})
  (doc:P.document) (symbols:TR.symbols u schema) (evidence:option (int & list int))
  : Lemma (requires Root.check_root_document_epsilon schema
                    (augment_with_evidence p doc evidence) == Root.RootCertified)
          (ensures not (Root.root_truths u schema
            (TR.standard u schema (FR.field_symbols u schema p symbols)) doc.P.assertions))
