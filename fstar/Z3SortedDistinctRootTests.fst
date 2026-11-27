module Z3SortedDistinctRootTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3ExprScope
module A = Z3DistinctAst
module R = Z3ClauseSyntax
module K = Z3SortedDistinct
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module DR = Z3SortedDistinctRoot

let int_sort = SortApp IntSymbol []
let x = Var 0 int_sort
let y = Var 1 int_sort
let duplicate = A.mk_distinct_expr int_sort [x; y; x]

let standard_duplicate (u:TR.uninterpreted) (sch:S.checked_schema)
                       (uf:TR.symbols u sch)
                       (rho:V.environment (TR.carrier u) (S.signature sch) [int_sort; int_sort])
  : Lemma (
      let i = TR.standard u sch (DR.standard_symbols u sch uf) in
      T.truth_at sch (TR.booleans u) (SR.root_scalars u) i [int_sort; int_sort] rho duplicate ==
      T.truth_at sch (TR.booleans u) (SR.root_scalars u) i [int_sort; int_sort] rho R.false_expr) =
  let i = TR.standard u sch (DR.standard_symbols u sch uf) in
  assert_norm (A.duplicate_rewrite duplicate R.false_expr);
  assert_norm (D.scoped [int_sort; int_sort] duplicate);
  DR.lemma_root_inhabited u sch uf;
  DR.lemma_distinct_model u sch uf;
  K.lemma_duplicate_rewrite sch (TR.booleans u) (SR.root_scalars u) i
    [int_sort; int_sort] rho duplicate R.false_expr

let lookalike_stays_free (u:TR.uninterpreted) (sch:S.checked_schema)
                         (uf:TR.symbols u sch)
                         (xs:TR.targuments u sch (A.distinct_decl int_sort 2).domain)
  : Lemma (
      let f = { A.distinct_decl int_sort 2 with int_params = [1] } in
      (DR.standard_symbols u sch uf).TR.apply f xs == uf.TR.apply f xs) =
  let f = { A.distinct_decl int_sort 2 with int_params = [1] } in
  assert_norm (not (A.distinct_declaration f));
  DR.lemma_preserves_other u sch uf f xs
