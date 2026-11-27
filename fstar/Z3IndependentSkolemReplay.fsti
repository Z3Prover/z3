module Z3IndependentSkolemReplay

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module P = Z3DocumentSyntax
module E = Z3SortedSkolem
module SK = Z3SkolemSyntax

val context (s:S.checked_schema) (doc:P.document)
  : ds:list (E.definition s){
      SK.ordered_context (E.erase s ds) /\ SK.fresh_inputs (E.erase s ds) doc.P.assertions}

val equations (s:S.checked_schema) (ds:list (E.definition s)) (entries:list P.entry)
  : list expr

val elaborate (s:S.checked_schema) (ds:list (E.definition s)) (doc:P.document)
  : result:P.document{
      result.P.assertions ==
        (if ds = [] then doc.P.assertions else doc.P.assertions @ equations s ds doc.P.entries) /\
      result.P.root == doc.P.root}

val lemma_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
  (ds:list (E.definition s)) (entries:list P.entry)
  : Lemma (requires E.context_model s bc eq other ds)
          (ensures T.truths s bc eq other (equations s ds entries))
