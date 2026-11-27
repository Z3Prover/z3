module Z3IndependentDefinitionNnfDocument

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module SP = Z3SortedProof
module Context = Z3IndependentDefinitionContext
module Def = Z3IndependentDefinitionDocument
module N = Z3IndependentDefinitionNnf
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot

let rec collect_acc (s:S.checked_schema) (inputs:list expr) (items:list (Context.item s inputs))
  (entries:list P.entry) (eqs:list expr) (rewritten:list P.entry)
  : Tot (list expr & list P.entry) (decreases entries) =
  match entries with
  | [] -> eqs, FStar.List.Tot.rev rewritten
  | e :: rest ->
    match N.candidate s inputs items e with
    | None -> collect_acc s inputs items rest eqs (e :: rewritten)
    | Some j -> collect_acc s inputs items rest (SP.proposition j :: eqs)
        ({ e with P.rule = U.Asserted } :: rewritten)

let collect (s:S.checked_schema) (inputs:list expr) (items:list (Context.item s inputs))
  (entries:list P.entry) : list expr & list P.entry =
  collect_acc s inputs items entries [] []

val augment (s:S.checked_schema) (doc:P.document)
  : result:P.document{
      let base = Def.augment s doc in
      let eqs, entries = collect s doc.P.assertions (Def.context s doc) base.P.entries in
      result.P.assertions == base.P.assertions @ eqs /\
      result.P.entries == entries /\ result.P.root == base.P.root}

val augment_prepared (s:S.checked_schema) (doc:P.document)
  (items:list (Context.item s doc.P.assertions){items == Def.context s doc})
  (base:P.document{base == Def.augment s doc})
  : result:P.document{result == augment s doc}

val lemma_equations_acc (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (items:list (Context.item s inputs)) (entries:list P.entry)
  (eqs:list expr) (rewritten:list P.entry)
  : Lemma (requires Q.forall_model s bc other /\
      T.truths s bc eq other (Context.formulas s inputs items) /\ T.truths s bc eq other eqs)
    (ensures T.truths s bc eq other (fst (collect_acc s inputs items entries eqs rewritten)))

val lemma_certified (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires Z3IndependentDefinitionDocument.eligible s doc /\
      Root.check_root_document s (augment s doc) == Root.RootCertified /\
      TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions))
