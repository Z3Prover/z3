module Z3IndependentDefinitionSkolemDocument

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module SP = Z3SortedProof
module Context = Z3IndependentDefinitionContext
module Definition = Z3IndependentDefinitionDocument
module Nnf = Z3IndependentDefinitionNnfDocument
module Combined = Z3IndependentDefinitionSkolemReplay
module Model = Z3IndependentSkolemModel
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module RL = Z3SortedReal
module RR = Z3SortedRealRoot
module Binder = Z3IndependentBinderElaboration
module L = FStar.List.Tot

let eligible (s:S.checked_schema) (doc:P.document) : bool =
  let items = Definition.context s doc in
  items <> [] && Context.ordered s doc.P.assertions items && Combined.compatible s doc items

let rec rewrite (formulas:list expr) (entries:list P.entry)
  : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    (if e.P.rule = U.DefinitionIntroduction && e.P.premise_ids = [] && L.mem e.P.formula formulas
     then { e with P.rule = U.Asserted } else e) :: rewrite formulas rest

let augment (s:S.checked_schema) (doc:P.document) : P.document =
  let items = Definition.context s doc in
  let prepared = Model.elaborate s doc in
  let formulas = Context.formulas s doc.P.assertions items in
  let entries = rewrite formulas prepared.P.entries in
  let eqs, rewritten = Nnf.collect s doc.P.assertions items entries in
  { prepared with P.assertions = (prepared.P.assertions @ formulas) @ eqs;
                  P.entries = rewritten }

let lemma_certified (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires eligible s doc /\
      Root.check_root_document s (augment s doc) == Root.RootCertified /\
      TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions)) =
  let bc = TR.booleans u in
  let eq = SR.root_scalars u in
  let choice = Root.root_choice u s in
  let items = Definition.context s doc in
  let extended = Combined.build s bc eq choice doc items other in
  let prepared = Model.elaborate s doc in
  let formulas = Context.formulas s doc.P.assertions items in
  let entries = rewrite formulas prepared.P.entries in
  Root.lemma_forall_model u s other;
  Root.lemma_exists_model u s other;
  Combined.lemma_build s bc eq choice doc items other;
  Combined.lemma_build_root u s bc eq choice doc items other;
  Nnf.lemma_equations_acc s bc eq extended doc.P.assertions items entries [] [];
  SP.lemma_truths_append s bc eq extended prepared.P.assertions formulas;
  SP.lemma_truths_append s bc eq extended (prepared.P.assertions @ formulas)
    (fst (Nnf.collect s doc.P.assertions items entries));
  Root.lemma_truths_agreement u s extended (augment s doc).P.assertions;
  Root.lemma_truths_agreement u s other doc.P.assertions;
  Root.lemma_root_certified u s (augment s doc) extended

let eligible_dependent (s:S.checked_schema) (doc:P.document) : bool =
  let items = Definition.context s doc in
  items <> [] && Context.ordered s doc.P.assertions items &&
    Combined.compatible_dependent s doc items

let augment_dependent (s:S.checked_schema) (doc:P.document) : P.document =
  let items = Definition.context s doc in
  let prepared = Model.elaborate_dependent s doc in
  let formulas = Context.formulas s doc.P.assertions items in
  let entries = rewrite formulas prepared.P.entries in
  let eqs, rewritten = Nnf.collect s doc.P.assertions items entries in
  { prepared with P.assertions = (prepared.P.assertions @ formulas) @ eqs;
                  P.entries = rewritten }

let lemma_certified_dependent (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires eligible_dependent s doc /\
      Root.check_root_document s (augment_dependent s doc) == Root.RootCertified /\
      TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions)) =
  let bc = TR.booleans u in
  let eq = SR.root_scalars u in
  let choice = Root.root_choice u s in
  let items = Definition.context s doc in
  let extended = Combined.build_dependent s bc eq choice doc items other in
  let prepared = Model.elaborate_dependent s doc in
  let formulas = Context.formulas s doc.P.assertions items in
  let entries = rewrite formulas prepared.P.entries in
  Root.lemma_forall_model u s other;
  Root.lemma_exists_model u s other;
  Combined.lemma_build_dependent s bc eq choice doc items other;
  Combined.lemma_build_dependent_root u s bc eq choice doc items other;
  Nnf.lemma_equations_acc s bc eq extended doc.P.assertions items entries [] [];
  SP.lemma_truths_append s bc eq extended prepared.P.assertions formulas;
  SP.lemma_truths_append s bc eq extended (prepared.P.assertions @ formulas)
    (fst (Nnf.collect s doc.P.assertions items entries));
  Root.lemma_truths_agreement u s extended (augment_dependent s doc).P.assertions;
  Root.lemma_truths_agreement u s other doc.P.assertions;
  Root.lemma_root_certified u s (augment_dependent s doc) extended

let augment_binder (s:S.checked_schema) (doc:P.document)
  : result:P.document{result == Binder.augment s (augment_dependent s doc)} =
  Binder.augment s (augment_dependent s doc)

let lemma_certified_binder (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires eligible_dependent s doc /\
      Root.check_root_document s (augment_binder s doc) == Root.RootCertified /\
      TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions)) =
  if Root.root_truths u s other doc.P.assertions then (
    let bc = TR.booleans u in
    let eq = SR.root_scalars u in
    let choice = Root.root_choice u s in
    let items = Definition.context s doc in
    let extended = Combined.build_dependent s bc eq choice doc items other in
    let prepared = Model.elaborate_dependent s doc in
    let formulas = Context.formulas s doc.P.assertions items in
    let entries = rewrite formulas prepared.P.entries in
    let expanded = augment_dependent s doc in
    Root.lemma_forall_model u s other;
    Root.lemma_exists_model u s other;
    Combined.lemma_build_dependent s bc eq choice doc items other;
    Combined.lemma_build_dependent_root u s bc eq choice doc items other;
    Nnf.lemma_equations_acc s bc eq extended doc.P.assertions items entries [] [];
    SP.lemma_truths_append s bc eq extended prepared.P.assertions formulas;
    SP.lemma_truths_append s bc eq extended (prepared.P.assertions @ formulas)
      (fst (Nnf.collect s doc.P.assertions items entries));
    Root.lemma_truths_agreement u s other doc.P.assertions;
    if RL.real_primitive s then RR.lemma_root_real_model u s extended;
    Binder.lemma_equations s bc eq extended expanded;
    SP.lemma_truths_append s bc eq extended expanded.P.assertions (Binder.equations s expanded);
    Root.lemma_truths_agreement u s extended (augment_binder s doc).P.assertions;
    Root.lemma_root_certified u s (augment_binder s doc) extended)
