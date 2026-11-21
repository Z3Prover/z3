module Z3IndependentCongruence

open Z3AstTheory
module S = Z3DatatypeSignature
module U = Z3UnifiedProofSyntax
module SP = Z3SortedProof
module D = Z3ExprScope
module NR = Z3NnfReplay

let application_congruence (s:S.checked_schema) (node:U.proof_node)
  : result:bool{
      result ==> node.U.kind == U.Congruence /\
                 SP.boolean_expression s (SP.proposition node.U.conclusion) /\
                 SP.consequence s (SP.propositions node.U.premises)
                                  (SP.proposition node.U.conclusion)} =
  match node.U.kind, node.U.conclusion with
  | U.Congruence, U.Equal a b ->
    (match a, b with
     | App f xs, App g ys ->
       let conclusion = SP.proposition node.U.conclusion in
       let facts = SP.propositions node.U.premises in
       if f = g && SP.boolean_expression s conclusion &&
          D.scoped_args [] facts && SP.equal_arguments_core s 7 facts xs ys then (
         assert (D.scoped [] a /\ D.scoped [] b /\ get_sort a == get_sort b);
         assert (SP.equal_core s 8 facts a b);
         assert (SP.equality_consequence s facts conclusion);
         true)
       else false
     | _, _ -> false)
  | _, _ -> false

let check_node (s:S.checked_schema) (assertions:list expr) (node:U.proof_node)
  : result:option (U.checked_fact & nat){
      result == SP.check_node_cached s assertions node} =
  if application_congruence s node then (
    assert (SP.nnf_verdict s assertions node == NR.Unreplayed);
    Some ({ U.conclusion = node.U.conclusion;
            hypotheses = U.premise_hypotheses node.U.premises }, 0))
  else SP.check_node_cached s assertions node
