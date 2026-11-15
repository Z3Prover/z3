module Z3IndependentDefinitionSkolem

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module SK = Z3SkolemSyntax
module E = Z3SortedSkolem
module DS = Z3SortedDependentSkolem
module Scope = Z3ExprScope
module L = FStar.List.Tot
module Q = Z3SortedQuantifier
module P = Z3DocumentSyntax
module SP = Z3SortedProof
module Context = Z3IndependentDefinitionContext
module TR = Z3TypedRoot
module Root = Z3SortedRootDocument
module DefinitionRoot = Z3IndependentDefinitionRoot

let rec lemma_closed_override_truths (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (d:E.definition s)
  (vs:V.arguments base (S.signature s) (L.rev d.SK.bound_sorts))
  (other:V.interpretation base (S.signature s)) (es:list expr)
  : Lemma (requires SK.fresh_args d.SK.witnesses es)
    (ensures T.truths s bc eq (E.override s d vs other) es == T.truths s bc eq other es)
    (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    if Scope.scoped [] e then
      E.lemma_fresh s bc eq other d vs [] (T.empty_environment (S.signature s)) e;
    lemma_closed_override_truths s bc eq d vs other rest

let rec lemma_closed_truths (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (ds:list (E.definition s)) (other:V.interpretation base (S.signature s)) (es:list expr)
  : Lemma (requires closed_fresh s ds es)
    (ensures T.truths s bc eq (E.build s bc eq choice ds other) es ==
             T.truths s bc eq other es)
    (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_closed_truths s bc eq choice rest other es;
    let older = E.build s bc eq choice rest other in
    lemma_closed_override_truths s bc eq d (E.selected s bc eq choice older d) older es

let rec lemma_dependent_override_truths (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (d:DS.definition s) (other:V.interpretation base (S.signature s)) (es:list expr)
  : Lemma (requires SK.fresh_args d.SK.witnesses es)
    (ensures T.truths s bc eq (DS.doverride s bc eq choice d other) es == T.truths s bc eq other es)
    (decreases es) =
  match es with
  | [] -> ()
  | e :: rest ->
    if Scope.scoped [] e then
      DS.lemma_fresh s bc eq choice d other [] (T.empty_environment (S.signature s)) e;
    lemma_dependent_override_truths s bc eq choice d other rest

let rec lemma_dependent_truths (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (ds:list (DS.definition s)) (other:V.interpretation base (S.signature s)) (es:list expr)
  : Lemma (requires dependent_fresh s ds es)
    (ensures T.truths s bc eq (DS.build s bc eq choice ds other) es ==
             T.truths s bc eq other es)
    (decreases ds) =
  match ds with
  | [] -> ()
  | d :: rest ->
    lemma_dependent_truths s bc eq choice rest other es;
    let older = DS.build s bc eq choice rest other in
    lemma_dependent_override_truths s bc eq choice d older es

let build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s)) =
  SP.full_extension s bc eq choice doc
    (Context.build s bc eq doc.P.assertions items other)

let lemma_build_expansion (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : Lemma (build s bc eq choice doc items other ==
    SP.full_extension s bc eq choice doc (Context.build s bc eq doc.P.assertions items other)) =
  ()

let lemma_build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (items:list (Context.item s doc.P.assertions))
  (other:V.interpretation base (S.signature s))
  : Lemma (requires Context.ordered s doc.P.assertions items /\ compatible s doc items /\
                    Q.forall_model s bc other /\ E.exists_model s bc other)
    (ensures (
      let extended = build s bc eq choice doc items other in
      T.truths s bc eq extended (Context.formulas s doc.P.assertions items) /\
      T.truths s bc eq extended doc.P.assertions == T.truths s bc eq other doc.P.assertions /\
      T.truths s bc eq extended
        (SP.epsilon_equations s (SP.epsilon_context s doc) doc.P.entries) /\
      T.truths s bc eq extended
        (DS.closures s (SP.dependent_context s doc (SP.epsilon_context s doc))) /\
      Q.forall_model s bc extended /\ E.exists_model s bc extended)) =
  let formulas = Context.formulas s doc.P.assertions items in
  let defined = Context.build s bc eq doc.P.assertions items other in
  let closed = SP.epsilon_context s doc in
  let dependent = SP.dependent_context s doc closed in
  let closed_model = E.build s bc eq choice closed defined in
  Context.lemma_build_inputs s bc eq doc.P.assertions items other;
  Context.lemma_build_quantification s bc eq doc.P.assertions items other;
  Context.lemma_build_context s bc eq doc.P.assertions items other;
  lemma_closed_truths s bc eq choice closed defined formulas;
  lemma_dependent_truths s bc eq choice dependent closed_model formulas;
  SP.lemma_full_extension s bc eq choice doc defined

let lemma_build_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (choice:E.hilbert_choice (TR.carrier u) s) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (build s bc eq choice doc items other)) =
  let defined = Context.build s bc eq doc.P.assertions items other in
  let closed = SP.epsilon_context s doc in
  let dependent = SP.dependent_context s doc closed in
  DefinitionRoot.lemma_build_root u s bc eq doc.P.assertions items other;
  Root.lemma_root_build u s bc eq choice closed defined;
  Root.lemma_root_dbuild u s bc eq choice dependent (E.build s bc eq choice closed defined)
