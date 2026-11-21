module Z3DistinctAstTests

open Z3AstTheory
module A = Z3DistinctAst
module R = Z3ClauseSyntax

let int_sort = SortApp IntSymbol []
let x = Var 0 int_sort
let y = Var 1 int_sort
let distinct = A.mk_distinct_expr int_sort [x; y]
let expansion = A.expanded [x; y]
let axiom =
  let args = [R.mk_not_expr distinct; expansion] in
  App (R.or_decl args) args
let malformed_axiom =
  let args = [R.mk_not_expr distinct; R.true_expr] in
  App (R.or_decl args) args

let recognizer_cases ()
  : Lemma (A.apply_lemma_distinct distinct == Some expansion /\
           A.expansion_rewrite distinct expansion /\
           A.distinct_axiom axiom /\ not (A.distinct_axiom malformed_axiom)) =
  assert_norm (A.apply_lemma_distinct distinct == Some expansion /\
               A.expansion_rewrite distinct expansion /\
               A.distinct_axiom axiom /\ not (A.distinct_axiom malformed_axiom))
