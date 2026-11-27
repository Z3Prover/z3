module Z3IndependentIteAdd

open Z3AstTheory
module D = Z3ExprScope
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

val check (lhs rhs:expr) : bool

val lemma_check (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (lhs rhs:expr)
  : Lemma (requires D.scoped scope lhs /\ D.scoped scope rhs /\ check lhs rhs)
          (ensures T.evaluate_at s bc model other scope rho lhs ==
                   T.evaluate_at s bc model other scope rho rhs)
