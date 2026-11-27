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
module DefinitionRoot = Z3IndependentDefinitionRoot
module Replay = Z3IndependentSkolemReplay
module DReplay = Z3IndependentDependentReplay
module Model = Z3IndependentSkolemModel
module TR = Z3TypedRoot

let build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s)) =
  Model.extension false s bc eq choice doc
    (Context.build s bc eq doc.P.assertions items other)

let lemma_build (#base:sort -> Type0) (s:S.checked_schema)
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
      Q.forall_model s bc extended /\ E.exists_model s bc extended)) =
  let defined = Context.build s bc eq doc.P.assertions items other in
  let closed = Replay.context s doc in
  let dependent = SP.dependent_context s doc closed in
  let formulas = Context.formulas s doc.P.assertions items in
  Context.lemma_build_inputs s bc eq doc.P.assertions items other;
  Context.lemma_build_quantification s bc eq doc.P.assertions items other;
  Context.lemma_build_context s bc eq doc.P.assertions items other;
  Model.lemma_extension false s bc eq choice doc defined;
  Model.lemma_extension_expansion s bc eq choice doc defined;
  Combined.lemma_closed_truths s bc eq choice closed defined formulas;
  Combined.lemma_dependent_truths s bc eq choice dependent
    (E.build s bc eq choice closed defined) formulas

let lemma_build_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (choice:E.hilbert_choice (TR.carrier u) s) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (build s bc eq choice doc items other)) =
  DefinitionRoot.lemma_build_root u s bc eq doc.P.assertions items other;
  Model.lemma_extension_root u false s bc eq choice doc
    (Context.build s bc eq doc.P.assertions items other)

let build_dependent (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s)) =
  Model.extension true s bc eq choice doc
    (Context.build s bc eq doc.P.assertions items other)

let lemma_build_dependent (#base:sort -> Type0) (s:S.checked_schema)
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
      Q.forall_model s bc extended /\ E.exists_model s bc extended)) =
  let defined = Context.build s bc eq doc.P.assertions items other in
  let closed = Replay.context s doc in
  let dependent = DReplay.context s doc closed in
  let formulas = Context.formulas s doc.P.assertions items in
  Context.lemma_build_inputs s bc eq doc.P.assertions items other;
  Context.lemma_build_quantification s bc eq doc.P.assertions items other;
  Context.lemma_build_context s bc eq doc.P.assertions items other;
  Model.lemma_extension true s bc eq choice doc defined;
  Model.lemma_extension_expansion_dependent s bc eq choice doc defined;
  Combined.lemma_closed_truths s bc eq choice closed defined formulas;
  Combined.lemma_dependent_truths s bc eq choice dependent
    (E.build s bc eq choice closed defined) formulas

let lemma_build_dependent_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (choice:E.hilbert_choice (TR.carrier u) s) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (build_dependent s bc eq choice doc items other)) =
  DefinitionRoot.lemma_build_root u s bc eq doc.P.assertions items other;
  Model.lemma_extension_root u true s bc eq choice doc
    (Context.build s bc eq doc.P.assertions items other)
