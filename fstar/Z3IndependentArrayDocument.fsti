module Z3IndependentArrayDocument

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module TR = Z3TypedRoot
module Root = Z3SortedRootDocument
module AP = Z3IndependentArrayPreservation
module A = Z3SortedArray
module AF = Z3IndependentArrayFamily
module SR = Z3SortedRoot
module SP = Z3SortedProof

let max_assertions : nat = 2000000

val eligible_entry (schema:S.schema) (entry:P.entry) : bool
val within_budget (doc:P.document) : bool
val has_candidates (schema:S.schema) (doc:P.document) : bool
val has_core_candidates (schema:S.checked_schema) (entries:list P.entry) : bool
val core_selected (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (if S.valid schema && within_budget doc &&
                    AP.eligible (S.signature schema) max_assertions doc.P.assertions &&
                    has_core_candidates schema doc.P.entries &&
                    SP.check_document_array schema doc == Some 0
                 then Some doc else None)}
val augment (schema:S.schema) (doc:P.document) : P.document
val selected (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (match core_selected schema doc with
        | Some selected -> Some selected
        | None -> if S.valid schema && within_budget doc &&
                    AP.eligible (S.signature schema) max_assertions doc.P.assertions &&
                    has_candidates schema doc &&
                    Root.check_root_document_epsilon schema (augment schema doc) == Root.RootCertified
                 then Some (augment schema doc) else None)}
val check (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == (match Root.check_root_document_epsilon schema doc with
        | Root.RootPending _ ->
          if Some? (selected schema doc) then Root.RootCertified
          else Root.check_root_document_epsilon schema doc
        | verdict -> verdict)}

val lemma_augment_truths_model (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires TR.root_model u schema model /\
                    A.model schema (TR.booleans u) (SR.root_scalars u) model
                      (AF.family u (S.signature schema)))
          (ensures Root.root_truths u schema model (augment schema doc).P.assertions ==
                   Root.root_truths u schema model doc.P.assertions)

val lemma_augment_truths (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires AP.eligible (S.signature schema) max_assertions doc.P.assertions)
          (ensures Root.root_truths u schema
                     (TR.standard u schema (Z3IndependentArrayInterpretation.symbols u schema symbols))
                     (augment schema doc).P.assertions ==
                   Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions)

val lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (symbols:TR.symbols u schema)
  : Lemma (requires check schema doc == Root.RootCertified)
          (ensures not (Root.root_truths u schema (TR.standard u schema symbols) doc.P.assertions))
