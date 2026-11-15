module Z3IndependentDefinitionEquivalence

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module Scope = Z3ExprScope
module Sub = Z3Substitution
module Model = Z3IndependentDefinitionModel

let instance_matches (d:D.definition) (a b:expr) : bool =
  match b with
  | App f [arg] ->
    f = d.D.symbol && f.domain = [get_sort arg] &&
    Sub.substitute [arg] d.D.body = Some a
  | _ -> false

let rec equivalent (fuel:nat) (d:D.definition) (a b:expr) : Tot bool (decreases %[fuel; a]) =
  if a = b then true
  else if fuel = 0 then false
  else if instance_matches d a b || instance_matches d b a then true
  else match a, b with
  | App f xs, App g ys -> f = g && equivalent_args (fuel - 1) d xs ys
  | Quantifier k bound r body, Quantifier k' bound' r' body' ->
    k = k' && bound = bound' && r = r' && get_sort body = get_sort body' &&
    equivalent (fuel - 1) d body body'
  | _, _ -> false

and equivalent_args (fuel:nat) (d:D.definition) (xs ys:list expr)
  : Tot bool (decreases %[fuel; xs]) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: tail -> equivalent fuel d x y && equivalent_args fuel d rest tail
  | _, _ -> false

val lemma_equivalent (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:Model.definition s inputs formula t)
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (fuel:nat) (a b:expr)
  : Lemma (requires Q.forall_model s bc other /\ T.truth s bc eq other formula /\
      Scope.scoped scope a /\ Scope.scoped scope b /\ equivalent fuel d a b)
    (ensures get_sort a == get_sort b /\
      T.evaluate_at s bc eq other scope rho a == T.evaluate_at s bc eq other scope rho b)
