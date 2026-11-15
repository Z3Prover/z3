module Z3IndependentCachedReplay

open Z3AstTheory
module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module SP = Z3SortedProof

val cache (s:S.checked_schema) (assertions:list expr) : Type0

val empty (s:S.checked_schema) (assertions:list expr) : cache s assertions

val seal (s:S.checked_schema) (assertions:list expr) (memo:cache s assertions)
  : cache s assertions

val check_entry (s:S.checked_schema) (assertions:list expr)
                (memo:cache s assertions) (index:nat) (entry:P.entry)
                (premises:option (list U.checked_fact))
  : result:(option (U.proof_node & U.checked_fact & nat) & cache s assertions){
      fst result ==
        (match SP.prepare_entry_from s premises entry with
         | None -> None
         | Some node ->
           match SP.check_node_cached s assertions node with
           | None -> None
           | Some (fact, local) -> Some (node, fact, local))}

val diagnose_document (s:S.checked_schema) (doc:P.document)
                      (memo:cache s doc.P.assertions)
  : result:(P.document_diagnostic & cache s doc.P.assertions){
      fst result == SP.diagnose_document s doc}
