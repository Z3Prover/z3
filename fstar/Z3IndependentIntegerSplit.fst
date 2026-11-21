module Z3IndependentIntegerSplit

open Z3AstTheory
module A = Z3LinearArithmeticAst
module AR = Z3SortedArithmetic
module D = Z3ExprScope
module G = Z3LpGomorySyntax
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let lemma_split (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (c:G.certificate)
  : Lemma (requires D.scoped scope c.split /\ get_sort c.split == A.int_s)
          (ensures T.truth_at s bc model other scope rho (G.branch false c) \/
                   T.truth_at s bc model other scope rho (G.branch true c)) =
  let low = G.integer c.threshold in
  let high = G.integer (c.threshold + 1) in
  assert (D.scoped scope low /\ D.scoped scope high);
  assert (D.scoped scope (G.branch false c) /\ D.scoped scope (G.branch true c));
  assert (A.comparison (G.branch false c) == Some (A.Le, c.split, low));
  assert (A.comparison (G.branch true c) == Some (A.Ge, c.split, high));
  AR.lemma_int_numeral s bc model other scope rho c.threshold low;
  AR.lemma_int_numeral s bc model other scope rho (c.threshold + 1) high;
  AR.lemma_int_comparison s bc model other scope rho (G.branch false c) A.Le c.split low;
  AR.lemma_int_comparison s bc model other scope rho (G.branch true c) A.Ge c.split high
