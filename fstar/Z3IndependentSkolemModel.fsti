module Z3IndependentSkolemModel

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module P = Z3DocumentSyntax
module E = Z3SortedSkolem
module DS = Z3SortedDependentSkolem
module Q = Z3SortedQuantifier
module RL = Z3SortedReal
module DV = Z3SortedIntDivision
module SP = Z3SortedProof
module Replay = Z3IndependentSkolemReplay
module DReplay = Z3IndependentDependentReplay
module Binder = Z3IndependentBinderElaboration
module TR = Z3TypedRoot

val elaborate (s:S.checked_schema) (doc:P.document) : P.document
val elaborate_dependent (s:S.checked_schema) (doc:P.document) : P.document
val elaborate_binder (s:S.checked_schema) (doc:P.document)
  : result:P.document{result == Binder.augment s (elaborate_dependent s doc)}
val check (schema:S.schema) (doc:P.document)
  : result:option nat{result == (if S.valid schema then SP.check_document schema (elaborate schema doc) else None)}
val check_dependent (schema:S.schema) (doc:P.document)
  : result:option nat{result == (if S.valid schema then SP.check_document schema (elaborate_dependent schema doc) else None)}
val check_binder (schema:S.schema) (doc:P.document)
  : result:option nat{result == (if S.valid schema then SP.check_document schema (elaborate_binder schema doc) else None)}

val lemma_same_dependent_context (s:S.checked_schema) (doc:P.document)
  : Lemma (requires DReplay.context s doc (Replay.context s doc) ==
                    SP.dependent_context s doc (Replay.context s doc))
          (ensures elaborate_dependent s doc == elaborate s doc /\
                   check_dependent s doc == check s doc)

val extension (#base:sort -> Type0) (larger:bool) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s))

val lemma_extension (#base:sort -> Type0) (larger:bool) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other)
    (ensures (let j = extension larger s bc eq choice doc other in
      Q.forall_model s bc j /\ E.exists_model s bc j /\
      T.truths s bc eq j (if larger then (elaborate_dependent s doc).P.assertions
                         else (elaborate s doc).P.assertions) ==
        T.truths s bc eq other doc.P.assertions))

val lemma_extension_root (u:TR.uninterpreted) (larger:bool) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (choice:E.hilbert_choice (TR.carrier u) s) (doc:P.document) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (extension larger s bc eq choice doc other))

val lemma_extension_expansion (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (
    let ds = Replay.context s doc in
    extension false s bc eq choice doc other ==
      DS.build s bc eq choice (SP.dependent_context s doc ds)
        (E.build s bc eq choice ds other))

val lemma_extension_expansion_dependent (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (
    let ds = Replay.context s doc in
    extension true s bc eq choice doc other ==
      DS.build s bc eq choice (DReplay.context s doc ds)
        (E.build s bc eq choice ds other))

val lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
  (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires check s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    DV.division_laws s bc eq other)
          (ensures not (T.truths s bc eq other doc.P.assertions))

val lemma_check_dependent (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
  (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires check_dependent s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    DV.division_laws s bc eq other)
          (ensures not (T.truths s bc eq other doc.P.assertions))

val lemma_check_binder (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
  (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires check_binder s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    DV.division_laws s bc eq other)
          (ensures not (T.truths s bc eq other doc.P.assertions))
