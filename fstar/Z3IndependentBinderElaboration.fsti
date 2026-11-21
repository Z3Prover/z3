module Z3IndependentBinderElaboration

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module RL = Z3SortedReal
module L = FStar.List.Tot

val candidate (s:S.checked_schema) (assertions:list expr) (entry:P.entry) : option U.judgment
val equations (s:S.checked_schema) (doc:P.document) : list expr
val augment (s:S.checked_schema) (doc:P.document)
  : result:P.document{
      result.P.assertions == doc.P.assertions @ equations s doc /\
      result.P.root == doc.P.root}

val augment_with_selection (s:S.checked_schema) (doc:P.document)
  : result:(P.document & list P.entry){fst result == augment s doc}

val lemma_selection (s:S.checked_schema) (doc:P.document) (entry:P.entry)
  : Lemma (ensures L.mem entry (snd (augment_with_selection s doc)) <==>
                   L.mem entry doc.P.entries /\ Some? (candidate s doc.P.assertions entry))

val lemma_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other doc.P.assertions)
          (ensures T.truths s bc eq other (equations s doc))
