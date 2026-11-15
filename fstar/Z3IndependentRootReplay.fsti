module Z3IndependentRootReplay

module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module Root = Z3SortedRootDocument
module SP = Z3SortedProof
module Fallback = Z3IndependentCertificateFallback

val check (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{result == Root.check_root_document_epsilon schema doc}

val check_diagnosed (schema:S.schema) (doc:P.document)
  : result:(Root.root_verdict & P.document_diagnostic){
      fst result == Root.check_root_document_epsilon schema doc /\
      snd result == snd (SP.check_document_epsilon_diagnosed schema doc)}

val check_recovering (schema:S.schema) (doc:P.document)
  : result:Root.root_verdict{
      result == Fallback.recover schema doc (Root.check_root_document_epsilon schema doc)}

val check_recovering_diagnosed (schema:S.schema) (doc:P.document)
  : result:(Root.root_verdict & P.document_diagnostic){
      fst result == Fallback.recover schema doc (Root.check_root_document_epsilon schema doc) /\
      snd result == snd (SP.check_document_epsilon_diagnosed schema doc)}
