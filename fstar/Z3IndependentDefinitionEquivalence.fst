module Z3IndependentDefinitionEquivalence

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module Scope = Z3ExprScope
module Model = Z3IndependentDefinitionModel
module Instance = Z3IndependentDefinitionInstance
module L = FStar.List.Tot

let rec lemma_equivalent (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:Model.definition s inputs formula)
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (fuel:nat) (a b:expr)
  : Lemma (requires d.D.symbol.domain == [t] /\ Q.forall_model s bc other /\
      T.truth s bc eq other formula /\
      Scope.scoped scope a /\ Scope.scoped scope b /\ equivalent fuel d a b)
    (ensures get_sort a == get_sort b /\
      T.evaluate_at s bc eq other scope rho a == T.evaluate_at s bc eq other scope rho b)
    (decreases %[fuel; a]) =
  if a = b then ()
  else if fuel = 0 then ()
  else if instance_matches d a b then (
    match b with
    | App _ [arg] -> Instance.lemma_instance s bc eq other inputs formula t d scope rho arg a
    | _ -> ())
  else if instance_matches d b a then (
    match a with
    | App _ [arg] -> Instance.lemma_instance s bc eq other inputs formula t d scope rho arg b
    | _ -> ())
  else match a, b with
  | App f xs, App _ ys ->
    lemma_equivalent_args s bc eq other inputs formula t d scope rho (fuel - 1) xs ys f.domain
  | Quantifier k bound _ body, Quantifier _ _ _ body' ->
    let at (vs:V.arguments base (S.signature s) (L.rev bound))
      : Lemma (T.evaluate_at s bc eq other (L.rev bound @ scope)
                 (V.extend (S.signature s) scope (L.rev bound) vs rho) body ==
               T.evaluate_at s bc eq other (L.rev bound @ scope)
                 (V.extend (S.signature s) scope (L.rev bound) vs rho) body') =
      lemma_equivalent s bc eq other inputs formula t d (L.rev bound @ scope)
        (V.extend (S.signature s) scope (L.rev bound) vs rho) (fuel - 1) body body' in
    FStar.Classical.forall_intro at;
    V.lemma_quantifier_environments (S.signature s) (T.interpretation s bc eq other)
      scope scope rho rho k bound (get_sort body) body body'
  | _, _ -> ()

and lemma_equivalent_args (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:Model.definition s inputs formula)
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (fuel:nat) (xs ys:list expr) (ss:list sort)
  : Lemma (requires d.D.symbol.domain == [t] /\ Q.forall_model s bc other /\
      T.truth s bc eq other formula /\
      Scope.scoped_args scope xs /\ Scope.scoped_args scope ys /\
      sorts_match xs ss /\ sorts_match ys ss /\ equivalent_args fuel d xs ys)
    (ensures V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho xs ss ==
             V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho ys ss)
    (decreases %[fuel; xs]) =
  match xs, ys, ss with
  | x :: rest, y :: tail, _ :: remaining ->
    lemma_equivalent s bc eq other inputs formula t d scope rho fuel x y;
    lemma_equivalent_args s bc eq other inputs formula t d scope rho fuel rest tail remaining
  | _, _, _ -> ()
