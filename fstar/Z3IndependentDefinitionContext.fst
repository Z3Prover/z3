module Z3IndependentDefinitionContext

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module Model = Z3IndependentDefinitionModel
module Scope = Z3ExprScope
module RL = Z3SortedReal
module DV = Z3SortedIntDivision

let rec build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s)) (decreases items) =
  match items with
  | [] -> other
  | d :: rest ->
    Model.override s bc eq (build s bc eq inputs rest other)
      inputs d.formula d.domain d.definition

let lemma_build_nil (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (other:V.interpretation base (S.signature s))
  : Lemma (build s bc eq inputs [] other == other) =
  ()

let lemma_build_cons (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (d:item s inputs) (rest:list (item s inputs))
  (other:V.interpretation base (S.signature s))
  : Lemma (build s bc eq inputs (d :: rest) other ==
    Model.override s bc eq (build s bc eq inputs rest other)
      inputs d.formula d.domain d.definition) =
  ()

let rec lemma_build_inputs (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (ensures T.truths s bc eq (build s bc eq inputs items other) inputs ==
                   T.truths s bc eq other inputs)
    (decreases items) =
  match items with
  | [] -> ()
  | d :: rest ->
    lemma_build_inputs s bc eq inputs rest other;
    Model.lemma_inputs s bc eq (build s bc eq inputs rest other)
      inputs d.formula d.domain d.definition

let rec lemma_build_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (ensures (Q.forall_model s bc (build s bc eq inputs items other) <==>
                    Q.forall_model s bc other) /\
                   (E.exists_model s bc (build s bc eq inputs items other) <==>
                    E.exists_model s bc other))
    (decreases items) =
  match items with
  | [] -> ()
  | d :: rest ->
    lemma_build_quantification s bc eq inputs rest other;
    Model.lemma_quantification s bc eq (build s bc eq inputs rest other)
      inputs d.formula d.domain d.definition

let rec lemma_build_real (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
    (ensures RL.real_laws s bc eq (build s bc eq inputs items other) reals)
    (decreases items) =
  match items with
  | [] -> ()
  | d :: rest ->
    lemma_build_real s bc eq inputs rest other reals;
    Model.lemma_real s bc eq (build s bc eq inputs rest other)
      inputs d.formula d.domain d.definition reals

let rec lemma_build_division (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (requires DV.division_laws s bc eq other)
    (ensures DV.division_laws s bc eq (build s bc eq inputs items other))
    (decreases items) =
  match items with
  | [] -> ()
  | d :: rest ->
    lemma_build_division s bc eq inputs rest other;
    Model.lemma_division s bc eq (build s bc eq inputs rest other)
      inputs d.formula d.domain d.definition

let rec lemma_preserve (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (newer:item s inputs) (items:list (item s inputs))
  (other:V.interpretation base (S.signature s))
  : Lemma (requires safe s inputs newer items)
    (ensures T.truths s bc eq
               (Model.override s bc eq other inputs newer.formula newer.domain newer.definition)
               (formulas s inputs items) ==
             T.truths s bc eq other (formulas s inputs items))
    (decreases items) =
  match items with
  | [] -> ()
  | d :: rest ->
    assert (Scope.scoped [] d.formula);
    Model.lemma_fresh s bc eq other inputs newer.formula newer.domain newer.definition
      [] (T.empty_environment (S.signature s)) d.formula;
    lemma_preserve s bc eq inputs newer rest other

let rec lemma_build_context (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (requires ordered s inputs items /\ Q.forall_model s bc other)
    (ensures T.truths s bc eq (build s bc eq inputs items other) (formulas s inputs items))
    (decreases items) =
  match items with
  | [] -> ()
  | d :: rest ->
    lemma_build_context s bc eq inputs rest other;
    lemma_build_quantification s bc eq inputs rest other;
    let older = build s bc eq inputs rest other in
    Model.lemma_definition s bc eq older inputs d.formula d.domain d.definition;
    lemma_preserve s bc eq inputs d rest older
