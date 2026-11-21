module Z3IndependentDependentReplay

open FStar.List.Tot
module S = Z3DatatypeSignature
module P = Z3DocumentSyntax
module E = Z3SortedSkolem
module DS = Z3SortedDependentSkolem
module SK = Z3SkolemSyntax
module SP = Z3SortedProof

val context (s:S.checked_schema) (doc:P.document)
            (closed:list (E.definition s){SK.ordered_context (E.erase s closed)})
  : dds:list (DS.definition s){
      SK.ordered_context (DS.erase s dds @ E.erase s closed) /\
      SK.fresh_inputs (DS.erase s dds) doc.P.assertions}

val may_change (s:S.checked_schema) (doc:P.document) : bool

val lemma_unchanged (s:S.checked_schema) (doc:P.document)
  (closed:list (E.definition s){SK.ordered_context (E.erase s closed)})
  : Lemma (requires not (may_change s doc))
          (ensures context s doc closed == SP.dependent_context s doc closed)
