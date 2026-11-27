module Z3SortedDistinct

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3ExprScope
module A = Z3DistinctAst

val distinct_from_at (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (core:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (a:expr{D.scoped scope a}) (args:list expr{D.scoped_args scope args}) : GTot bool

val distinct_values_at (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (core:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (args:list expr{D.scoped_args scope args}) : GTot bool

val lemma_from_nil (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (core:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (a:expr{D.scoped scope a})
  : Lemma (distinct_from_at s bc core other scope rho a [] == true)

val lemma_from_cons (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (core:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (a:expr{D.scoped scope a}) (b:expr{D.scoped scope b})
  (rest:list expr{D.scoped_args scope rest})
  : Lemma (distinct_from_at s bc core other scope rho a (b :: rest) ==
           (not (T.equal_tree core.reflection (T.evaluate_at s bc core other scope rho a)
                                               (T.evaluate_at s bc core other scope rho b)) &&
            distinct_from_at s bc core other scope rho a rest))

val lemma_values_nil (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (core:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  : Lemma (distinct_values_at s bc core other scope rho [] == true)

val lemma_values_cons (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (core:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (a:expr{D.scoped scope a}) (rest:list expr{D.scoped_args scope rest})
  : Lemma (distinct_values_at s bc core other scope rho (a :: rest) ==
           (distinct_from_at s bc core other scope rho a rest &&
            distinct_values_at s bc core other scope rho rest))

unfold let model (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (core:T.scalar_model base)
  (other:V.interpretation base (S.signature s)) : prop =
  forall (scope:list sort) (rho:V.environment base (S.signature s) scope)
         (f:func_decl) (args:list expr).
    D.scoped scope (App f args) /\ A.distinct_app f args ==>
    (T.truth_at s bc core other scope rho (App f args) ==
     distinct_values_at s bc core other scope rho args)

val lemma_duplicate_rewrite (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (core:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (a b:expr)
  : Lemma (requires model s bc core other /\ D.scoped scope a /\
                    A.duplicate_rewrite a b)
          (ensures T.truth_at s bc core other scope rho a ==
                   T.truth_at s bc core other scope rho b)
