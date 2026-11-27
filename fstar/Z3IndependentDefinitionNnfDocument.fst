module Z3IndependentDefinitionNnfDocument

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module P = Z3DocumentSyntax
module SP = Z3SortedProof
module Context = Z3IndependentDefinitionContext
module Combined = Z3IndependentDefinitionSkolem
module Def = Z3IndependentDefinitionDocument
module N = Z3IndependentDefinitionNnf
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module SR = Z3SortedRoot

let augment (s:S.checked_schema) (doc:P.document) : P.document =
  let base = Def.augment s doc in
  let items = Def.context s doc in
  let eqs, entries = collect s doc.P.assertions items base.P.entries in
  { base with
    P.assertions = base.P.assertions @ eqs;
    P.entries = entries }

let augment_prepared (s:S.checked_schema) (doc:P.document)
  (items:list (Context.item s doc.P.assertions){items == Def.context s doc})
  (base:P.document{base == Def.augment s doc})
  : result:P.document{result == augment s doc} =
  let eqs, entries = collect s doc.P.assertions items base.P.entries in
  { base with P.assertions = base.P.assertions @ eqs; P.entries = entries }

let rec lemma_equations_acc (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (items:list (Context.item s inputs)) (entries:list P.entry)
  (eqs:list expr) (rewritten:list P.entry)
  : Lemma (requires Q.forall_model s bc other /\
      T.truths s bc eq other (Context.formulas s inputs items) /\ T.truths s bc eq other eqs)
    (ensures T.truths s bc eq other (fst (collect_acc s inputs items entries eqs rewritten)))
    (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    (match N.candidate s inputs items e with
     | None -> lemma_equations_acc s bc eq other inputs items rest eqs (e :: rewritten)
     | Some j ->
       N.lemma_candidate s bc eq other inputs items e j;
       lemma_equations_acc s bc eq other inputs items rest (SP.proposition j :: eqs)
         ({ e with P.rule = Z3UnifiedProofSyntax.Asserted } :: rewritten))

let lemma_certified (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires Def.eligible s doc /\
      Root.check_root_document s (augment s doc) == Root.RootCertified /\
      TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions)) =
  let bc = TR.booleans u in
  let eq = SR.root_scalars u in
  let choice = Root.root_choice u s in
  let items = Def.context s doc in
  let defined = Context.build s bc eq doc.P.assertions items other in
  let extended = Combined.build s bc eq choice doc items other in
  Def.lemma_eligible s doc;
  Def.lemma_augment_assertions s doc;
  Root.lemma_forall_model u s other;
  Root.lemma_exists_model u s other;
  Context.lemma_build_quantification s bc eq doc.P.assertions items other;
  Context.lemma_build_inputs s bc eq doc.P.assertions items other;
  Combined.lemma_build s bc eq choice doc items other;
  Combined.lemma_build_expansion s bc eq choice doc items other;
  Combined.lemma_build_root u s bc eq choice doc items other;
  SP.lemma_full_extension s bc eq choice doc defined;
  lemma_equations_acc s bc eq extended doc.P.assertions items (Def.augment s doc).P.entries [] [];
  SP.lemma_truths_append s bc eq extended (SP.elaborate_full s doc).P.assertions
    (Context.formulas s doc.P.assertions items);
  SP.lemma_truths_append s bc eq extended (Def.augment s doc).P.assertions
    (fst (collect s doc.P.assertions items (Def.augment s doc).P.entries));
  Root.lemma_truths_agreement u s extended (augment s doc).P.assertions;
  Root.lemma_truths_agreement u s other doc.P.assertions;
  Root.lemma_root_certified u s (augment s doc) extended
