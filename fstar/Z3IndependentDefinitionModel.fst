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
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  : V.interpretation base (S.signature s) =
  assert (Scope.scoped [t] d.D.body /\ get_sort d.D.body == d.D.symbol.range);
  {
    V.application = (fun f args ->
      if f = d.D.symbol then
        let env = V.extend (S.signature s) [] [t] args (T.empty_environment (S.signature s)) in
        T.evaluate_at s bc eq other [t] env d.D.body
      else other.V.application f args);
    V.quantification = other.V.quantification;
  }

let lemma_override_application (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  (f:func_decl) (args:V.arguments base (S.signature s) f.domain)
  : Lemma (requires f <> d.D.symbol)
    (ensures (override s bc eq other inputs formula t d).V.application f args ==
             other.V.application f args) =
  ()

let lemma_override_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  : Lemma ((override s bc eq other inputs formula t d).V.quantification ==
           other.V.quantification) =
  ()

let lemma_application_fresh (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  (f:func_decl) (args:V.arguments base (S.signature s) f.domain)
  : Lemma (requires f <> d.D.symbol)
    (ensures T.application s bc eq other f args ==
             T.application s bc eq (override s bc eq other inputs formula t d) f args) =
  ()

let rec lemma_fresh (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  (scope:list sort) (rho:V.environment base (S.signature s) scope) (e:expr)
  : Lemma (requires Scope.scoped scope e /\ D.fresh [d] e)
    (ensures T.evaluate_at s bc eq other scope rho e ==
             T.evaluate_at s bc eq (override s bc eq other inputs formula t d) scope rho e)
    (decreases e) =
  match e with
  | Var _ _ -> ()
  | App f args ->
    lemma_fresh_args s bc eq other inputs formula t d scope rho args f.domain;
    lemma_application_fresh s bc eq other inputs formula t d f
      (V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho args f.domain)
  | Quantifier _ bound _ body ->
    let pointwise (ws:V.arguments base (S.signature s) (L.rev bound))
      : Lemma (
          T.evaluate_at s bc eq other (L.rev bound @ scope)
            (V.extend (S.signature s) scope (L.rev bound) ws rho) body ==
          T.evaluate_at s bc eq (override s bc eq other inputs formula t d) (L.rev bound @ scope)
            (V.extend (S.signature s) scope (L.rev bound) ws rho) body) =
      lemma_fresh s bc eq other inputs formula t d (L.rev bound @ scope)
        (V.extend (S.signature s) scope (L.rev bound) ws rho) body in
    FStar.Classical.forall_intro pointwise;
    let left = V.evaluate_body (S.signature s) (T.interpretation s bc eq other) scope rho bound body in
    let right = V.evaluate_body (S.signature s)
      (T.interpretation s bc eq (override s bc eq other inputs formula t d)) scope rho bound body in
    assert (FE.feq_g left right);
    FE.extensionality_g (V.arguments base (S.signature s) (L.rev bound)) (fun _ -> V.tree base) left right

and lemma_fresh_args (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  (scope:list sort) (rho:V.environment base (S.signature s) scope)
  (args:list expr) (ss:list sort)
  : Lemma (requires Scope.scoped_args scope args /\ sorts_match args ss /\ D.fresh_args [d] args)
    (ensures V.evaluate_args (S.signature s) (T.interpretation s bc eq other) scope rho args ss ==
             V.evaluate_args (S.signature s)
               (T.interpretation s bc eq (override s bc eq other inputs formula t d)) scope rho args ss)
    (decreases args) =
  match args, ss with
  | e :: rest, _ :: tail ->
    lemma_fresh s bc eq other inputs formula t d scope rho e;
    lemma_fresh_args s bc eq other inputs formula t d scope rho rest tail
  | _, _ -> ()

let rec lemma_inputs_aux (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  (es:list expr)
  : Lemma (requires D.fresh_args [d] es)
    (ensures T.truths s bc eq (override s bc eq other inputs formula t d) es ==
             T.truths s bc eq other es)
    (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    if Scope.scoped [] e then
      lemma_fresh s bc eq other inputs formula t d [] (T.empty_environment (S.signature s)) e;
    lemma_inputs_aux s bc eq other inputs formula t d rest

let lemma_inputs (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  : Lemma (ensures T.truths s bc eq (override s bc eq other inputs formula t d) inputs ==
                   T.truths s bc eq other inputs) =
  lemma_inputs_aux s bc eq other inputs formula t d inputs

let lemma_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  : Lemma (ensures (Q.forall_model s bc (override s bc eq other inputs formula t d) <==>
                    Q.forall_model s bc other) /\
                   (E.exists_model s bc (override s bc eq other inputs formula t d) <==>
                    E.exists_model s bc other)) =
  ()

let lemma_real (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
    (ensures RL.real_laws s bc eq (override s bc eq other inputs formula t d) reals) =
  let extended = override s bc eq other inputs formula t d in
  introduce forall (f:func_decl) (args:V.arguments base (S.signature s) f.domain).
    ~(RL.Other? (RL.classify f)) ==> extended.V.application f args == other.V.application f args
  with (
    if not (RL.Other? (RL.classify f)) && f = d.D.symbol then
      RL.lemma_classified_tag f);
  RL.lemma_real_laws_transfer s bc eq other extended reals

let lemma_division (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  : Lemma (requires DV.division_laws s bc eq other)
    (ensures DV.division_laws s bc eq (override s bc eq other inputs formula t d)) =
  let extended = override s bc eq other inputs formula t d in
  introduce forall (f:func_decl) (args:V.arguments base (S.signature s) f.domain).
    ~(DV.Other? (DV.classify f)) ==> extended.V.application f args == other.V.application f args
  with (
    if not (DV.Other? (DV.classify f)) && f = d.D.symbol then
      DV.lemma_classified_tag f);
  DV.lemma_division_laws_transfer s bc eq other extended

let lemma_pointwise (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  (rho:V.environment base (S.signature s) [t])
  : Lemma (
    let extended = override s bc eq other inputs formula t d in
    T.truth_at s bc eq extended [t] rho (App d.D.symbol [Var 0 t]) <==>
    T.truth_at s bc eq extended [t] rho d.D.body) =
  let extended = override s bc eq other inputs formula t d in
  let args = [rho 0] in
  let env = V.extend (S.signature s) [] [t] args (T.empty_environment (S.signature s)) in
  lemma_fresh s bc eq other inputs formula t d [t] env d.D.body;
  let at (n:nat{n < L.length [t]}) : Lemma (env n == rho n) = () in
  FStar.Classical.forall_intro at;
  Q.lemma_free_environments (S.signature s) (T.interpretation s bc eq extended) [t] env rho d.D.body;
  Dependent.lemma_safe_application s bc eq extended d.D.symbol args

let lemma_definition (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula t)
  : Lemma (requires Q.forall_model s bc other)
    (ensures T.truth s bc eq (override s bc eq other inputs formula t d) formula) =
  let extended = override s bc eq other inputs formula t d in
  lemma_quantification s bc eq other inputs formula t d;
  let at (rho:V.environment base (S.signature s) [t])
    : Lemma (T.truth_at s bc eq extended [t] rho (App d.D.symbol [Var 0 t]) <==>
             T.truth_at s bc eq extended [t] rho d.D.body) =
    lemma_pointwise s bc eq other inputs formula t d rho in
  FStar.Classical.forall_intro at;
  Pair.lemma_pair_truth s bc eq extended inputs formula d t
