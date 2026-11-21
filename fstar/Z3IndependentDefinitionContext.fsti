module Z3IndependentDefinitionContext

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module Model = Z3IndependentDefinitionModel
module RL = Z3SortedReal
module DV = Z3SortedIntDivision

type item (s:S.checked_schema) (inputs:list expr) = {
  formula: expr;
  domain: sort;
  definition: Model.definition s inputs formula domain;
}

let rec safe (s:S.checked_schema) (inputs:list expr)
             (newer:item s inputs) (older:list (item s inputs))
  : Tot bool (decreases older) =
  match older with
  | [] -> true
  | d :: rest -> D.fresh [newer.definition] d.formula && safe s inputs newer rest

let rec ordered (s:S.checked_schema) (inputs:list expr) (items:list (item s inputs))
  : Tot bool (decreases items) =
  match items with
  | [] -> true
  | d :: rest -> safe s inputs d rest && ordered s inputs rest

let rec formulas (s:S.checked_schema) (inputs:list expr) (items:list (item s inputs))
  : Tot (list expr) (decreases items) =
  match items with [] -> [] | d :: rest -> d.formula :: formulas s inputs rest

val build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s))

val lemma_build_nil (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (other:V.interpretation base (S.signature s))
  : Lemma (build s bc eq inputs [] other == other)

val lemma_build_cons (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (d:item s inputs) (rest:list (item s inputs))
  (other:V.interpretation base (S.signature s))
  : Lemma (build s bc eq inputs (d :: rest) other ==
    Model.override s bc eq (build s bc eq inputs rest other)
      inputs d.formula d.domain d.definition)

val lemma_build_inputs (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (ensures T.truths s bc eq (build s bc eq inputs items other) inputs ==
                   T.truths s bc eq other inputs)

val lemma_build_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (ensures (Q.forall_model s bc (build s bc eq inputs items other) <==>
                    Q.forall_model s bc other) /\
                   (E.exists_model s bc (build s bc eq inputs items other) <==>
                    E.exists_model s bc other))

val lemma_build_real (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
    (ensures RL.real_laws s bc eq (build s bc eq inputs items other) reals)

val lemma_build_division (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (requires DV.division_laws s bc eq other)
    (ensures DV.division_laws s bc eq (build s bc eq inputs items other))

val lemma_build_context (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (requires ordered s inputs items /\ Q.forall_model s bc other)
    (ensures T.truths s bc eq (build s bc eq inputs items other) (formulas s inputs items))
