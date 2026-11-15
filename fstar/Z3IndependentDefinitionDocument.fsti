module Z3IndependentDefinitionDocument

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module Context = Z3IndependentDefinitionContext
module Combined = Z3IndependentDefinitionSkolem
module SP = Z3SortedProof
module Root = Z3SortedRootDocument
module TR = Z3TypedRoot
module U = Z3UnifiedProofSyntax

let rec has_definition (entries:list P.entry) : Tot bool (decreases entries) =
  match entries with
  | [] -> false
  | e :: rest -> e.P.rule = U.DefinitionIntroduction || has_definition rest

val context (s:S.checked_schema) (doc:P.document)
  : list (Context.item s doc.P.assertions)
val augment (s:S.checked_schema) (doc:P.document) : P.document
val eligible_context (s:S.checked_schema) (doc:P.document)
  (items:list (Context.item s doc.P.assertions))
  : result:bool{result == (items <> [] && Context.ordered s doc.P.assertions items &&
      Combined.compatible s doc items)}
val eligible (s:S.checked_schema) (doc:P.document)
  : result:bool{result == eligible_context s doc (context s doc)}

val lemma_no_definitions (s:S.checked_schema) (doc:P.document)
  : Lemma (requires not (has_definition doc.P.entries))
          (ensures not (eligible s doc))

val prepare (s:S.checked_schema) (doc:P.document)
  : result:(list (Context.item s doc.P.assertions) & P.document){
      fst result == context s doc /\ snd result == SP.elaborate_full s doc}

val augment_prepared (s:S.checked_schema) (doc:P.document)
  (items:list (Context.item s doc.P.assertions){items == context s doc})
  (prepared:P.document{prepared == SP.elaborate_full s doc})
  : result:P.document{result == augment s doc}

val lemma_eligible (s:S.checked_schema) (doc:P.document)
  : Lemma (requires eligible s doc)
    (ensures Context.ordered s doc.P.assertions (context s doc) /\
      Combined.compatible s doc (context s doc))

val lemma_augment_assertions (s:S.checked_schema) (doc:P.document)
  : Lemma ((augment s doc).P.assertions ==
    (SP.elaborate_full s doc).P.assertions @ Context.formulas s doc.P.assertions (context s doc))

val lemma_certified (u:TR.uninterpreted) (s:S.checked_schema)
  (doc:P.document) (other:TR.interp u s)
  : Lemma (requires eligible s doc /\ Root.check_root_document s (augment s doc) == Root.RootCertified /\
                    TR.root_model u s other)
    (ensures not (Root.root_truths u s other doc.P.assertions))
