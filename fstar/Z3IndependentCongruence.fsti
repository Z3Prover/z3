module Z3IndependentCongruence

open Z3AstTheory
module S = Z3DatatypeSignature
module U = Z3UnifiedProofSyntax
module SP = Z3SortedProof

val check_node (s:S.checked_schema) (assertions:list expr) (node:U.proof_node)
  : result:option (U.checked_fact & nat){
      result == SP.check_node_cached s assertions node}
