module Z3UnifiedNode

open Z3AstTheory
open Z3ClauseSyntax
open Z3UnifiedProofSyntax
module SK = Z3SkolemSyntax

let check_node_with_membership
    (check_step:rule -> judgment -> list judgment -> Tot bool)
    (checked_theory_lemma:rule -> judgment -> list judgment -> Tot bool)
    (check_binder_with_context:
       list SK.definition -> list judgment -> binder_certificate -> judgment -> Tot bool)
    (skolems:list SK.definition) (strict:bool)
    (assertions:list judgment) (contains:judgment -> bool) (node:proof_node)
  : option (checked_fact & nat) =
  let facts = premise_judgments node.premises in
  let hyps = premise_hypotheses node.premises in
  let accept hs n = Some ({ conclusion = node.conclusion; hypotheses = hs }, n) in
  if not (well_formed node.conclusion && judgments_wf facts && scopes_wf node.premises) then None
  else
    match node.kind with
    | Asserted ->
      if facts = [] && Some? (proposition node.conclusion) && contains node.conclusion
      then accept [] 0 else None
    | DefAxiom ->
      if facts = [] && Some? (proposition node.conclusion)
      then accept [] (if check_step DefAxiom node.conclusion facts then 0 else 1)
      else None
    | Hypothesis ->
      (match facts, proposition node.conclusion with
       | [], Some e -> accept [e] 0
       | _, _ -> None)
    | LemmaRule ->
      (match facts, proposition node.conclusion with
       | [j], Some e ->
         if false_judgment j && boolean_formulas (formula_clause e)
         then accept (remaining_hypotheses hyps e) 0 else None
       | _, _ -> None)
    | Unverified _ | ArithmeticFarkas _ | ArithmeticBound _ | ArithmeticGomory _ | ArithmeticLattice _ | FiniteFieldPac _ ->
      accept hyps (if checked_theory_lemma node.kind node.conclusion facts then 0 else 1)
    | RewriteRule | PullQuantifier | ElimUnused | PushQuantifier
    | DestructiveEquality | DestructiveEqualityResolution ->
      if facts = [] && Some? (relational node.conclusion)
      then accept hyps (if check_step node.kind node.conclusion facts then 0 else 1)
      else None
    | Skolemization ->
      if facts = [] && Observational? node.conclusion
      then accept [] (if skolem_step skolems node.conclusion facts then 0 else 1)
      else None
    | QuantifierIntroduction certificate ->
      if facts = [] && Some? (relational node.conclusion)
      then accept [] (if check_binder_with_context skolems assertions certificate node.conclusion then 0 else 1)
      else None
    | QuantifierInstantiation _ ->
      if facts = [] && Some? (proposition node.conclusion)
      then accept [] (if check_step node.kind node.conclusion facts then 0 else 1)
      else None
    | _ -> if check_step node.kind node.conclusion facts then accept hyps 0 else None
