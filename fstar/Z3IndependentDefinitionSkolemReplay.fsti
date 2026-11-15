module Z3IndependentDefinitionSkolemReplay

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module E = Z3SortedSkolem
module Q = Z3SortedQuantifier
module P = Z3DocumentSyntax
module SP = Z3SortedProof
module Context = Z3IndependentDefinitionContext
module Combined = Z3IndependentDefinitionSkolem
module Replay = Z3IndependentSkolemReplay
module DReplay = Z3IndependentDependentReplay
module Model = Z3IndependentSkolemModel
module TR = Z3TypedRoot

let compatible (s:S.checked_schema) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) : bool =
  let closed = Replay.context s doc in
  let dependent = SP.dependent_context s doc closed in
  let formulas = Context.formulas s doc.P.assertions items in
  Combined.closed_fresh s closed formulas && Combined.dependent_fresh s dependent formulas

let compatible_dependent (s:S.checked_schema) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) : bool =
  let closed = Replay.context s doc in
  let dependent = DReplay.context s doc closed in
  let formulas = Context.formulas s doc.P.assertions items in
  Combined.closed_fresh s closed formulas && Combined.dependent_fresh s dependent formulas

val build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s))

val lemma_build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : Lemma (requires Context.ordered s doc.P.assertions items /\ compatible s doc items /\
      Q.forall_model s bc other /\ E.exists_model s bc other)
    (ensures (
      let extended = build s bc eq choice doc items other in
      T.truths s bc eq extended (Context.formulas s doc.P.assertions items) /\
      T.truths s bc eq extended (Model.elaborate s doc).P.assertions ==
        T.truths s bc eq other doc.P.assertions /\
      Q.forall_model s bc extended /\ E.exists_model s bc extended))

val lemma_build_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (choice:E.hilbert_choice (TR.carrier u) s) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (build s bc eq choice doc items other))

val build_dependent (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s))

val lemma_build_dependent (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : Lemma (requires Context.ordered s doc.P.assertions items /\ compatible_dependent s doc items /\
      Q.forall_model s bc other /\ E.exists_model s bc other)
    (ensures (
      let extended = build_dependent s bc eq choice doc items other in
      T.truths s bc eq extended (Context.formulas s doc.P.assertions items) /\
      T.truths s bc eq extended (Model.elaborate_dependent s doc).P.assertions ==
        T.truths s bc eq other doc.P.assertions /\
      Q.forall_model s bc extended /\ E.exists_model s bc extended))

val lemma_build_dependent_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (choice:E.hilbert_choice (TR.carrier u) s) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (build_dependent s bc eq choice doc items other))
