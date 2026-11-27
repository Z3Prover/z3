module Z3IndependentDefinitionModel

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module Dependent = Z3SortedDependentSkolem
module Pair = Z3IndependentDefinitionPair
module Scope = Z3ExprScope
module FE = FStar.FunctionalExtensionality
module L = FStar.List.Tot
module RL = Z3SortedReal
module DV = Z3SortedIntDivision

let override (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : V.interpretation base (S.signature s) =
  assert (Pair.valid s inputs formula d);
  {
    V.application = (fun f args ->
      if f = d.D.symbol then
        match d.D.symbol.domain with
        | [] -> T.evaluate s bc eq other d.D.body
        | [t] ->
          let env = V.extend (S.signature s) [] [t] args (T.empty_environment (S.signature s)) in
          T.evaluate_at s bc eq other [t] env d.D.body
        | _ -> other.V.application f args
      else other.V.application f args);
    V.quantification = other.V.quantification;
  }

let lemma_override_application (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (f:func_decl) (args:V.arguments base (S.signature s) f.domain)
  : Lemma (requires f <> d.D.symbol)
    (ensures (override s bc eq other inputs formula d).V.application f args ==
             other.V.application f args) =
  ()

let lemma_override_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma ((override s bc eq other inputs formula d).V.quantification ==
           other.V.quantification) =
  ()

let lemma_application_fresh (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (f:func_decl) (args:V.arguments base (S.signature s) f.domain)
  : Lemma (requires f <> d.D.symbol)
    (ensures T.application s bc eq other f args ==
             T.application s bc eq (override s bc eq other inputs formula d) f args) =
  ()

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
    lemma_fresh_args s bc eq other inputs formula d scope rho args f.domain;
    lemma_application_fresh s bc eq other inputs formula d f
      (V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho args f.domain)
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
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (es:list expr)
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
  : Lemma (ensures T.truths s bc eq (override s bc eq other inputs formula d) inputs ==
                   T.truths s bc eq other inputs) =
  lemma_inputs_aux s bc eq other inputs formula d inputs

let lemma_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (ensures (Q.forall_model s bc (override s bc eq other inputs formula d) <==>
                    Q.forall_model s bc other) /\
                   (E.exists_model s bc (override s bc eq other inputs formula d) <==>
                    E.exists_model s bc other)) =
  ()

let lemma_real (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
    (ensures RL.real_laws s bc eq (override s bc eq other inputs formula d) reals) =
  let extended = override s bc eq other inputs formula d in
  introduce forall (f:func_decl) (args:V.arguments base (S.signature s) f.domain).
    ~(RL.Other? (RL.classify f)) ==> extended.V.application f args == other.V.application f args
  with (
    if not (RL.Other? (RL.classify f)) && f = d.D.symbol then
      RL.lemma_classified_tag f);
  RL.lemma_real_laws_transfer s bc eq other extended reals

let lemma_division (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (requires DV.division_laws s bc eq other)
    (ensures DV.division_laws s bc eq (override s bc eq other inputs formula d)) =
  let extended = override s bc eq other inputs formula d in
  introduce forall (f:func_decl) (args:V.arguments base (S.signature s) f.domain).
    ~(DV.Other? (DV.classify f)) ==> extended.V.application f args == other.V.application f args
  with (
    if not (DV.Other? (DV.classify f)) && f = d.D.symbol then
      DV.lemma_classified_tag f);
  DV.lemma_division_laws_transfer s bc eq other extended

let lemma_pointwise (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula)
  (rho:V.environment base (S.signature s) [t])
  : Lemma (requires d.D.symbol.domain == [t])
    (ensures T.truth_at s bc eq (override s bc eq other inputs formula d) [t] rho
                    (App d.D.symbol [Var 0 t]) <==>
             T.truth_at s bc eq (override s bc eq other inputs formula d) [t] rho d.D.body) =
  let extended = override s bc eq other inputs formula d in
  let args = [rho 0] in
  let env = V.extend (S.signature s) [] [t] args (T.empty_environment (S.signature s)) in
  lemma_fresh s bc eq other inputs formula d [t] env d.D.body;
  let at (n:nat{n < L.length [t]}) : Lemma (env n == rho n) = () in
  FStar.Classical.forall_intro at;
  Q.lemma_free_environments (S.signature s) (T.interpretation s bc eq extended) [t] env rho d.D.body;
  Dependent.lemma_safe_application s bc eq extended d.D.symbol args

let lemma_definition (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (requires Q.forall_model s bc other)
    (ensures T.truth s bc eq (override s bc eq other inputs formula d) formula) =
  let extended = override s bc eq other inputs formula d in
  lemma_quantification s bc eq other inputs formula d;
  match d.D.symbol.domain with
  | [t] ->
    let at (rho:V.environment base (S.signature s) [t])
      : Lemma (T.truth_at s bc eq extended [t] rho (App d.D.symbol [Var 0 t]) <==>
               T.truth_at s bc eq extended [t] rho d.D.body) =
      lemma_pointwise s bc eq other inputs formula t d rho in
    FStar.Classical.forall_intro at;
    Pair.lemma_pair_truth s bc eq extended inputs formula d t
  | [] ->
    let name = App d.D.symbol [] in
    lemma_fresh s bc eq other inputs formula d [] (T.empty_environment (S.signature s)) d.D.body;
    Dependent.lemma_safe_application s bc eq extended d.D.symbol [];
    T.lemma_equality s bc eq extended name d.D.body;
    assert (T.evaluate s bc eq extended name == T.evaluate s bc eq extended d.D.body);
    Pair.lemma_scalar_pair_truth s bc eq extended inputs formula d
  | _ -> ()
