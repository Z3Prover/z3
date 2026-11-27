module Z3IndependentCertificateFallback

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module R = Z3SortedRootDocument
module T = Z3TypedRoot

val has_candidates (entries:list P.entry) : Tot bool

val repair (doc:P.document)
  : result:P.document{result.P.assertions == doc.P.assertions}

val recover (schema:S.schema) (doc:P.document) (base:R.root_verdict)
  : result:R.root_verdict{
      (base <> R.RootUncovered ==> result == base) /\
      (base == R.RootUncovered ==> (result == base \/ result == R.RootCertified)) /\
      result == (if base = R.RootUncovered && has_candidates doc.P.entries &&
                    R.check_root_document_epsilon schema (repair doc) = R.RootCertified
                 then R.RootCertified else base)}

val lemma_certified (u:T.uninterpreted) (schema:S.checked_schema)
                    (doc:P.document) (base:R.root_verdict) (model:T.interp u schema)
  : Lemma (requires base == R.check_root_document_epsilon schema doc /\
                    recover schema doc base == R.RootCertified /\ T.root_model u schema model)
          (ensures not (R.root_truths u schema model doc.P.assertions))
