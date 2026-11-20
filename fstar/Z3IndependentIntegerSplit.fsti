module Z3IndependentIntegerSplit

open Z3AstTheory
module D = Z3ExprScope
module G = Z3LpGomorySyntax
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue
module A = Z3LinearArithmeticAst

val lemma_split (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (c:G.certificate)
  : Lemma (requires D.scoped scope c.split /\ get_sort c.split == A.int_s)
          (ensures T.truth_at s bc model other scope rho (G.branch false c) \/
                   T.truth_at s bc model other scope rho (G.branch true c))
