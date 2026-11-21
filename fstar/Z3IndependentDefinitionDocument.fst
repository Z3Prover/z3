module Z3IndependentDefinitionDocument

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module Pair = Z3IndependentDefinitionPair
module Context = Z3IndependentDefinitionContext
module Combined = Z3IndependentDefinitionSkolem
module SP = Z3SortedProof
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module SR = Z3SortedRoot
module T = Z3SortedSemantics
module L = FStar.List.Tot
module E = Z3SortedSkolem

let item (s:S.checked_schema) (inputs:list expr) (entry:P.entry)
  : option (Context.item s inputs) =
  if entry.P.rule <> U.DefinitionIntroduction || entry.P.premise_ids <> [] then None
  else match Pair.recognize s inputs entry.P.formula with
  | None -> None
  | Some d ->
    match d.D.symbol.domain with
    | [t] -> Some { Context.formula = entry.P.formula; domain = t; definition = d }
    | _ -> None

let rec collect (s:S.checked_schema) (inputs:list expr) (entries:list P.entry)
  (acc:list (Context.item s inputs)) : Tot (list (Context.item s inputs)) (decreases entries) =
  match entries with
  | [] -> acc
  | e :: rest ->
    (match item s inputs e with
     | None -> collect s inputs rest acc
     | Some d -> collect s inputs rest (d :: acc))

let context (s:S.checked_schema) (doc:P.document) : list (Context.item s doc.P.assertions) =
  collect s doc.P.assertions (SP.elaborate_full s doc).P.entries []

let rec rewrite_entries (s:S.checked_schema) (inputs:list expr) (entries:list P.entry)
  : Tot (list P.entry) (decreases entries) =
  match entries with
  | [] -> []
  | e :: rest ->
    (if Some? (item s inputs e) then { e with P.rule = U.Asserted } else e) ::
      rewrite_entries s inputs rest

let augment (s:S.checked_schema) (doc:P.document) : P.document =
  let prepared = SP.elaborate_full s doc in
  let items = collect s doc.P.assertions prepared.P.entries [] in
  { prepared with
    P.assertions = prepared.P.assertions @ Context.formulas s doc.P.assertions items;
    P.entries = rewrite_entries s doc.P.assertions prepared.P.entries }

let eligible_context (s:S.checked_schema) (doc:P.document)
  (items:list (Context.item s doc.P.assertions)) : bool =
  items <> [] && Context.ordered s doc.P.assertions items && Combined.compatible s doc items

let eligible (s:S.checked_schema) (doc:P.document) : bool =
  eligible_context s doc (context s doc)

let rec lemma_collect_no_definitions (s:S.checked_schema) (inputs:list expr)
  (entries:list P.entry) (acc:list (Context.item s inputs))
  : Lemma (requires not (has_definition entries))
          (ensures collect s inputs entries acc == acc)
          (decreases entries) =
  match entries with
  | [] -> ()
  | _ :: rest -> lemma_collect_no_definitions s inputs rest acc

let rec lemma_epsilon_no_definitions (s:S.checked_schema) (ds:list (E.definition s))
  (entries:list P.entry)
  : Lemma (requires not (has_definition entries))
          (ensures not (has_definition (SP.epsilon_entries s ds entries)))
          (decreases entries) =
  match entries with
  | [] -> ()
  | _ :: rest -> lemma_epsilon_no_definitions s ds rest

let lemma_no_definitions (s:S.checked_schema) (doc:P.document)
  : Lemma (requires not (has_definition doc.P.entries))
          (ensures not (eligible s doc)) =
  let ds = SP.epsilon_context s doc in
  lemma_epsilon_no_definitions s ds doc.P.entries;
  lemma_collect_no_definitions s doc.P.assertions (SP.elaborate_full s doc).P.entries []

let prepare (s:S.checked_schema) (doc:P.document)
  : result:(list (Context.item s doc.P.assertions) & P.document){
      fst result == context s doc /\ snd result == SP.elaborate_full s doc} =
  let prepared = SP.elaborate_full s doc in
  let items = collect s doc.P.assertions prepared.P.entries [] in
  items, prepared

let augment_prepared (s:S.checked_schema) (doc:P.document)
  (items:list (Context.item s doc.P.assertions){items == context s doc})
  (prepared:P.document{prepared == SP.elaborate_full s doc})
  : result:P.document{result == augment s doc} =
  { prepared with
    P.assertions = prepared.P.assertions @ Context.formulas s doc.P.assertions items;
    P.entries = rewrite_entries s doc.P.assertions prepared.P.entries }

let lemma_eligible (s:S.checked_schema) (doc:P.document)
  : Lemma (requires eligible s doc)
    (ensures Context.ordered s doc.P.assertions (context s doc) /\
      Combined.compatible s doc (context s doc)) = ()

let lemma_augment_assertions (s:S.checked_schema) (doc:P.document)
  : Lemma ((augment s doc).P.assertions ==
    (SP.elaborate_full s doc).P.assertions @ Context.formulas s doc.P.assertions (context s doc)) = ()

let lemma_certified (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires eligible s doc /\ Root.check_root_document s (augment s doc) == Root.RootCertified /\
                    TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions)) =
  let bc = TR.booleans u in
  let eq = SR.root_scalars u in
  let choice = Root.root_choice u s in
  let items = context s doc in
  let defined = Context.build s bc eq doc.P.assertions items other in
  let extended = Combined.build s bc eq choice doc items other in
  Root.lemma_forall_model u s other;
  Root.lemma_exists_model u s other;
  Context.lemma_build_quantification s bc eq doc.P.assertions items other;
  Context.lemma_build_inputs s bc eq doc.P.assertions items other;
  Combined.lemma_build s bc eq choice doc items other;
  Combined.lemma_build_expansion s bc eq choice doc items other;
  Combined.lemma_build_root u s bc eq choice doc items other;
  SP.lemma_full_extension s bc eq choice doc defined;
  SP.lemma_truths_append s bc eq extended (SP.elaborate_full s doc).P.assertions
    (Context.formulas s doc.P.assertions items);
  Root.lemma_truths_agreement u s extended (augment s doc).P.assertions;
  Root.lemma_truths_agreement u s other doc.P.assertions;
  Root.lemma_root_certified u s (augment s doc) extended
