module Z3SortedDistinctTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3ExprScope
module A = Z3DistinctAst
module R = Z3ClauseSyntax
module K = Z3SortedDistinct

let int_sort = SortApp IntSymbol []
let x = Var 0 int_sort
let y = Var 1 int_sort
let duplicate = A.mk_distinct_expr int_sort [x; y; x]
let different = A.mk_distinct_expr int_sort [x; y]

let semantic_values (#base:sort -> Type0) (s:S.checked_schema)
                    (bc:S.boolean_carrier base) (core:T.scalar_model base)
                    (other:V.interpretation base (S.signature s))
                    (rho:V.environment base (S.signature s) [int_sort; int_sort])
  : Lemma (
      not (K.distinct_values_at s bc core other [int_sort; int_sort] rho [x; x]) /\
      (K.distinct_values_at s bc core other [int_sort; int_sort] rho [x; y] <==>
       ~(T.evaluate_at s bc core other [int_sort; int_sort] rho x ==
         T.evaluate_at s bc core other [int_sort; int_sort] rho y))) =
  let scope = [int_sort; int_sort] in
  assert_norm (D.scoped scope x /\ D.scoped scope y);
  K.lemma_values_cons s bc core other scope rho x [x];
  K.lemma_from_cons s bc core other scope rho x x [];
  K.lemma_values_cons s bc core other scope rho x [y];
  K.lemma_from_cons s bc core other scope rho x y [];
  K.lemma_from_nil s bc core other scope rho x;
  K.lemma_values_cons s bc core other scope rho y [];
  K.lemma_from_nil s bc core other scope rho y;
  K.lemma_values_nil s bc core other scope rho;
  T.lemma_equal_tree core.reflection (T.evaluate_at s bc core other scope rho x)
                                    (T.evaluate_at s bc core other scope rho x);
  T.lemma_equal_tree core.reflection (T.evaluate_at s bc core other scope rho x)
                                    (T.evaluate_at s bc core other scope rho y)

let duplicate_is_sound (#base:sort -> Type0) (s:S.checked_schema)
                       (bc:S.boolean_carrier base) (core:T.scalar_model base)
                       (other:V.interpretation base (S.signature s))
                       (rho:V.environment base (S.signature s) [int_sort; int_sort])
  : Lemma (requires K.model s bc core other)
          (ensures T.truth_at s bc core other [int_sort; int_sort] rho duplicate ==
                   T.truth_at s bc core other [int_sort; int_sort] rho R.false_expr) =
  assert_norm (A.duplicate_rewrite duplicate R.false_expr);
  assert_norm (D.scoped [int_sort; int_sort] duplicate);
  K.lemma_duplicate_rewrite s bc core other [int_sort; int_sort] rho duplicate R.false_expr

let recognizer_rejects_mutants ()
  : Lemma (not (A.duplicate_rewrite different R.false_expr) /\
           not (A.duplicate_rewrite duplicate R.true_expr) /\
           not (A.duplicate_rewrite
             (App ({ A.distinct_decl int_sort 2 with int_params = [1] }) [x; x]) R.false_expr)) =
  assert_norm (not (A.duplicate_rewrite different R.false_expr) /\
               not (A.duplicate_rewrite duplicate R.true_expr) /\
               not (A.duplicate_rewrite
                 (App ({ A.distinct_decl int_sort 2 with int_params = [1] }) [x; x]) R.false_expr))
