module Z3IndependentGroundDocument

open FStar.List.Tot
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module TR = Z3TypedRoot
module Root = Z3SortedRootDocument
module Ground = Z3IndependentGroundDefinition

type choice (schema:S.checked_schema) (doc:P.document) =
  c:(P.entry & D.definition){
    (fst c).P.rule == U.DefinitionIntroduction /\
    (fst c).P.premise_ids == [] /\
    Ground.valid schema doc.P.assertions (fst c).P.formula (snd c)}

val within_budget (doc:P.document) : bool
val choose (schema:S.checked_schema) (doc:P.document) : option (choice schema doc)
val augment (doc:P.document) (entry:P.entry)
  : result:P.document{result.P.assertions == doc.P.assertions @ [entry.P.formula]}
val selected (schema:S.schema) (doc:P.document)
  : result:option P.document{
      result == (if S.valid schema && within_budget doc then
                   match choose schema doc with
                   | Some c ->
                     if Root.check_root_document_epsilon schema (augment doc (fst c)) == Root.RootCertified
                     then Some (augment doc (fst c)) else None
                   | None -> None
                 else None)}

val selected_expanded (schema:S.schema) (doc:P.document) : option P.document

val lemma_certified (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires Some? (selected schema doc) /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))

val lemma_certified_expanded (u:TR.uninterpreted) (schema:S.checked_schema)
  (doc:P.document) (model:TR.interp u schema)
  : Lemma (requires Some? (selected_expanded schema doc) /\ TR.root_model u schema model)
          (ensures not (Root.root_truths u schema model doc.P.assertions))
