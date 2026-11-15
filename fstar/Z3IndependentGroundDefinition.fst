module Z3IndependentGroundDefinition

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Scope = Z3ExprScope
module Dependent = Z3SortedDependentSkolem
module R = Z3ClauseSyntax
module FE = FStar.FunctionalExtensionality
module L = FStar.List.Tot

let override (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : V.interpretation base (S.signature s) =
  { V.application = (fun f args ->
      if f = d.D.symbol then T.evaluate s bc eq other d.D.body
      else other.V.application f args);
    V.quantification = other.V.quantification }

let lemma_override_application (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (f:func_decl) (args:V.arguments base (S.signature s) f.domain)
  : Lemma (requires f <> d.D.symbol)
    (ensures (override s bc eq other inputs formula d).V.application f args ==
             other.V.application f args) = ()

let lemma_override_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma ((override s bc eq other inputs formula d).V.quantification ==
           other.V.quantification) = ()

let rec lemma_fresh (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (scope:list sort) (rho:V.environment base (S.signature s) scope) (e:expr)
  : Lemma (requires Scope.scoped scope e /\ D.fresh [d] e)
    (ensures T.evaluate_at s bc eq other scope rho e ==
             T.evaluate_at s bc eq (override s bc eq other inputs formula d) scope rho e)
    (decreases e) =
  match e with
  | Var _ _ -> ()
  | App f args ->
    lemma_fresh_args s bc eq other inputs formula d scope rho args f.domain
  | Quantifier _ bound _ body ->
    let pointwise (ws:V.arguments base (S.signature s) (L.rev bound))
      : Lemma (
          T.evaluate_at s bc eq other (L.rev bound @ scope)
            (V.extend (S.signature s) scope (L.rev bound) ws rho) body ==
          T.evaluate_at s bc eq (override s bc eq other inputs formula d) (L.rev bound @ scope)
            (V.extend (S.signature s) scope (L.rev bound) ws rho) body) =
      lemma_fresh s bc eq other inputs formula d (L.rev bound @ scope)
        (V.extend (S.signature s) scope (L.rev bound) ws rho) body in
    FStar.Classical.forall_intro pointwise;
    let left = V.evaluate_body (S.signature s) (T.interpretation s bc eq other) scope rho bound body in
    let right = V.evaluate_body (S.signature s)
      (T.interpretation s bc eq (override s bc eq other inputs formula d)) scope rho bound body in
    assert (FE.feq_g left right);
    FE.extensionality_g (V.arguments base (S.signature s) (L.rev bound)) (fun _ -> V.tree base) left right

and lemma_fresh_args (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (args:list expr) (ss:list sort)
  : Lemma (requires Scope.scoped_args scope args /\ sorts_match args ss /\ D.fresh_args [d] args)
    (ensures V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho args ss ==
             V.evaluate_args (S.signature s)
               (T.interpretation s bc eq (override s bc eq other inputs formula d)) scope rho args ss)
    (decreases args) =
  match args, ss with
  | e :: rest, _ :: tail ->
    lemma_fresh s bc eq other inputs formula d scope rho e;
    lemma_fresh_args s bc eq other inputs formula d scope rho rest tail
  | _, _ -> ()

let rec lemma_inputs_aux (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula) (es:list expr)
  : Lemma (requires D.fresh_args [d] es)
    (ensures T.truths s bc eq (override s bc eq other inputs formula d) es ==
             T.truths s bc eq other es)
    (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    if Scope.scoped [] e then
      lemma_fresh s bc eq other inputs formula d [] (T.empty_environment (S.signature s)) e;
    lemma_inputs_aux s bc eq other inputs formula d rest

let lemma_inputs (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (T.truths s bc eq (override s bc eq other inputs formula d) inputs ==
           T.truths s bc eq other inputs) =
  lemma_inputs_aux s bc eq other inputs formula d inputs

let lemma_definition (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (T.truth s bc eq (override s bc eq other inputs formula d) formula) =
  let extended = override s bc eq other inputs formula d in
  let name = App d.D.symbol [] in
  lemma_fresh s bc eq other inputs formula d [] (T.empty_environment (S.signature s)) d.D.body;
  Dependent.lemma_safe_application s bc eq extended d.D.symbol [];
  T.lemma_equality s bc eq extended name d.D.body;
  T.lemma_equality s bc eq extended d.D.body name
