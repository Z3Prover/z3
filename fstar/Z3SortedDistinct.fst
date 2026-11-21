module Z3SortedDistinct

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module D = Z3ExprScope
module A = Z3DistinctAst
module R = Z3ClauseSyntax
module L = FStar.List.Tot

let rec distinct_from_at (#base:sort -> Type0) (s:S.checked_schema)
                         (bc:S.boolean_carrier base) (core:T.scalar_model base)
                         (other:V.interpretation base (S.signature s))
                         (scope:list sort) (rho:V.environment base (S.signature s) scope)
                         (a:expr{D.scoped scope a})
                         (args:list expr{D.scoped_args scope args})
  : GTot bool (decreases args) =
  match args with
  | [] -> true
  | b :: rest ->
    not (T.equal_tree core.reflection (T.evaluate_at s bc core other scope rho a)
                                    (T.evaluate_at s bc core other scope rho b)) &&
    distinct_from_at s bc core other scope rho a rest

let rec distinct_values_at (#base:sort -> Type0) (s:S.checked_schema)
                           (bc:S.boolean_carrier base) (core:T.scalar_model base)
                           (other:V.interpretation base (S.signature s))
                           (scope:list sort) (rho:V.environment base (S.signature s) scope)
                           (args:list expr{D.scoped_args scope args})
  : GTot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest ->
    distinct_from_at s bc core other scope rho a rest &&
    distinct_values_at s bc core other scope rho rest

let lemma_from_nil (#base:sort -> Type0) (s:S.checked_schema)
                   (bc:S.boolean_carrier base) (core:T.scalar_model base)
                   (other:V.interpretation base (S.signature s))
                   (scope:list sort) (rho:V.environment base (S.signature s) scope)
                   (a:expr{D.scoped scope a})
  : Lemma (distinct_from_at s bc core other scope rho a [] == true) = ()

let lemma_from_cons (#base:sort -> Type0) (s:S.checked_schema)
                    (bc:S.boolean_carrier base) (core:T.scalar_model base)
                    (other:V.interpretation base (S.signature s))
                    (scope:list sort) (rho:V.environment base (S.signature s) scope)
                    (a:expr{D.scoped scope a}) (b:expr{D.scoped scope b})
                    (rest:list expr{D.scoped_args scope rest})
  : Lemma (distinct_from_at s bc core other scope rho a (b :: rest) ==
           (not (T.equal_tree core.reflection (T.evaluate_at s bc core other scope rho a)
                                               (T.evaluate_at s bc core other scope rho b)) &&
            distinct_from_at s bc core other scope rho a rest)) = ()

let lemma_values_nil (#base:sort -> Type0) (s:S.checked_schema)
                     (bc:S.boolean_carrier base) (core:T.scalar_model base)
                     (other:V.interpretation base (S.signature s))
                     (scope:list sort) (rho:V.environment base (S.signature s) scope)
  : Lemma (distinct_values_at s bc core other scope rho [] == true) = ()

let lemma_values_cons (#base:sort -> Type0) (s:S.checked_schema)
                      (bc:S.boolean_carrier base) (core:T.scalar_model base)
                      (other:V.interpretation base (S.signature s))
                      (scope:list sort) (rho:V.environment base (S.signature s) scope)
                      (a:expr{D.scoped scope a}) (rest:list expr{D.scoped_args scope rest})
  : Lemma (distinct_values_at s bc core other scope rho (a :: rest) ==
           (distinct_from_at s bc core other scope rho a rest &&
            distinct_values_at s bc core other scope rho rest)) = ()

let rec lemma_repeated (#base:sort -> Type0) (s:S.checked_schema)
                       (bc:S.boolean_carrier base) (core:T.scalar_model base)
                       (other:V.interpretation base (S.signature s))
                       (scope:list sort) (rho:V.environment base (S.signature s) scope)
                       (a:expr{D.scoped scope a})
                       (args:list expr{D.scoped_args scope args})
  : Lemma (requires L.mem a args)
          (ensures not (distinct_from_at s bc core other scope rho a args))
          (decreases args) =
  match args with
  | [] -> ()
  | b :: rest ->
    if a = b then T.lemma_equal_tree core.reflection
      (T.evaluate_at s bc core other scope rho a)
      (T.evaluate_at s bc core other scope rho b)
    else lemma_repeated s bc core other scope rho a rest

let rec lemma_duplicate (#base:sort -> Type0) (s:S.checked_schema)
                        (bc:S.boolean_carrier base) (core:T.scalar_model base)
                        (other:V.interpretation base (S.signature s))
                        (scope:list sort) (rho:V.environment base (S.signature s) scope)
                        (args:list expr{D.scoped_args scope args})
  : Lemma (requires A.has_duplicate args)
          (ensures not (distinct_values_at s bc core other scope rho args))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    if L.mem a rest then lemma_repeated s bc core other scope rho a rest
    else lemma_duplicate s bc core other scope rho rest

let lemma_duplicate_rewrite (#base:sort -> Type0) (s:S.checked_schema)
                            (bc:S.boolean_carrier base) (core:T.scalar_model base)
                            (other:V.interpretation base (S.signature s))
                            (scope:list sort) (rho:V.environment base (S.signature s) scope)
                            (a b:expr)
  : Lemma (requires model s bc core other /\ D.scoped scope a /\
                    A.duplicate_rewrite a b)
          (ensures T.truth_at s bc core other scope rho a ==
                   T.truth_at s bc core other scope rho b) =
  match a with
  | App f args ->
    lemma_duplicate s bc core other scope rho args;
    T.lemma_evaluate_core_at s bc core other scope rho
      (match R.false_expr with App g _ -> g | _ -> f) []
  | _ -> ()
