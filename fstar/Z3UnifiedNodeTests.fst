module Z3UnifiedNodeTests

open Z3ClauseSyntax
open Z3UnifiedProofSyntax
module N = Z3UnifiedNode

let accepted_step _ _ _ = true
let rejected_step _ _ _ = false
let accepted_binder _ _ _ _ = true

let rewrite : proof_node = {
  kind = RewriteRule;
  conclusion = Equal true_expr false_expr;
  premises = [];
}

let theory : proof_node = {
  kind = Unverified "th-lemma";
  conclusion = Holds true_expr;
  premises = [];
}

let dispatch_and_obligations ()
  : Lemma (
      N.check_node_with_membership accepted_step rejected_step accepted_binder [] false [] (fun _ -> false) rewrite ==
        Some ({ conclusion = rewrite.conclusion; hypotheses = [] }, 0) /\
      N.check_node_with_membership rejected_step rejected_step accepted_binder [] false [] (fun _ -> false) rewrite ==
        Some ({ conclusion = rewrite.conclusion; hypotheses = [] }, 1) /\
      N.check_node_with_membership accepted_step rejected_step accepted_binder [] false [] (fun _ -> false)
        { rewrite with premises = [{ conclusion = Holds true_expr; hypotheses = [] }] } == None /\
      N.check_node_with_membership rejected_step accepted_step accepted_binder [] false [] (fun _ -> false) theory ==
        Some ({ conclusion = theory.conclusion; hypotheses = [] }, 0) /\
      N.check_node_with_membership accepted_step rejected_step accepted_binder [] false [] (fun _ -> false) theory ==
        Some ({ conclusion = theory.conclusion; hypotheses = [] }, 1)) =
  assert_norm (
    N.check_node_with_membership accepted_step rejected_step accepted_binder [] false [] (fun _ -> false) rewrite ==
      Some ({ conclusion = rewrite.conclusion; hypotheses = [] }, 0) /\
    N.check_node_with_membership rejected_step rejected_step accepted_binder [] false [] (fun _ -> false) rewrite ==
      Some ({ conclusion = rewrite.conclusion; hypotheses = [] }, 1) /\
    N.check_node_with_membership accepted_step rejected_step accepted_binder [] false [] (fun _ -> false)
      { rewrite with premises = [{ conclusion = Holds true_expr; hypotheses = [] }] } == None /\
    N.check_node_with_membership rejected_step accepted_step accepted_binder [] false [] (fun _ -> false) theory ==
      Some ({ conclusion = theory.conclusion; hypotheses = [] }, 0) /\
    N.check_node_with_membership accepted_step rejected_step accepted_binder [] false [] (fun _ -> false) theory ==
      Some ({ conclusion = theory.conclusion; hypotheses = [] }, 1))
