module Z3IndependentSkolemModel

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module P = Z3DocumentSyntax
module E = Z3SortedSkolem
module DS = Z3SortedDependentSkolem
module Q = Z3SortedQuantifier
module RL = Z3SortedReal
module RX = Z3SortedRealExtension
module DV = Z3SortedIntDivision
module DX = Z3SortedDivisionExtension
module SP = Z3SortedProof
module Replay = Z3IndependentSkolemReplay
module DReplay = Z3IndependentDependentReplay
module Binder = Z3IndependentBinderElaboration
module TR = Z3TypedRoot
module Root = Z3SortedRootDocument

let dependent_context (larger:bool) (s:S.checked_schema) (doc:P.document)
                      (ds:list (E.definition s){Z3SkolemSyntax.ordered_context (E.erase s ds)})
  : dds:list (DS.definition s){
      Z3SkolemSyntax.ordered_context (DS.erase s dds @ E.erase s ds) /\
      Z3SkolemSyntax.fresh_inputs (DS.erase s dds) doc.P.assertions} =
  if larger then DReplay.context s doc ds else SP.dependent_context s doc ds

let elaborate_with (larger:bool) (s:S.checked_schema) (doc:P.document) : P.document =
  let ds = Replay.context s doc in
  SP.elaborate_dependent s (dependent_context larger s doc ds) (Replay.elaborate s ds doc)

let elaborate (s:S.checked_schema) (doc:P.document) : P.document = elaborate_with false s doc
let elaborate_dependent (s:S.checked_schema) (doc:P.document) : P.document = elaborate_with true s doc
let elaborate_binder (s:S.checked_schema) (doc:P.document) : P.document =
  Binder.augment s (elaborate_dependent s doc)

let check_with (larger:bool) (schema:S.schema) (doc:P.document) : option nat =
  if S.valid schema then SP.check_document schema (elaborate_with larger schema doc) else None

let check (schema:S.schema) (doc:P.document) : option nat = check_with false schema doc
let check_dependent (schema:S.schema) (doc:P.document) : option nat = check_with true schema doc
let check_binder (schema:S.schema) (doc:P.document) : option nat =
  if S.valid schema then SP.check_document schema (elaborate_binder schema doc) else None

let lemma_same_dependent_context (s:S.checked_schema) (doc:P.document)
  : Lemma (requires DReplay.context s doc (Replay.context s doc) ==
                    SP.dependent_context s doc (Replay.context s doc))
          (ensures elaborate_dependent s doc == elaborate s doc /\
                   check_dependent s doc == check s doc) =
  ()

let extension (#base:sort -> Type0) (larger:bool) (s:S.checked_schema) (bc:S.boolean_carrier base)
              (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
              (doc:P.document) (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s)) =
  let ds = Replay.context s doc in
  DS.build s bc eq choice (dependent_context larger s doc ds) (E.build s bc eq choice ds other)

let lemma_extension (#base:sort -> Type0) (larger:bool) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                    (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other)
          (ensures (let j = extension larger s bc eq choice doc other in
                    Q.forall_model s bc j /\ E.exists_model s bc j /\
                    T.truths s bc eq j (elaborate_with larger s doc).P.assertions ==
                      T.truths s bc eq other doc.P.assertions)) =
  let ds = Replay.context s doc in
  let dds = dependent_context larger s doc ds in
  let e1 = E.build s bc eq choice ds other in
  let j = DS.build s bc eq choice dds e1 in
  E.lemma_build_context s bc eq choice ds other;
  E.lemma_build_inputs s bc eq choice ds other doc.P.assertions;
  E.lemma_build_quantification s bc eq choice ds other;
  E.lemma_quantification_models s bc other e1;
  DS.lemma_ordered_append (DS.erase s dds) (E.erase s ds);
  DS.lemma_build_context s bc eq choice dds e1;
  DS.lemma_build_inputs s bc eq choice dds e1 doc.P.assertions;
  DS.lemma_build_closed s bc eq choice dds e1 ds;
  DS.lemma_build_quantification s bc eq choice dds e1;
  E.lemma_quantification_models s bc e1 j;
  Replay.lemma_equations s bc eq j ds doc.P.entries;
  DS.lemma_context_truths s bc eq j dds;
  SP.lemma_truths_append s bc eq j doc.P.assertions (Replay.equations s ds doc.P.entries);
  SP.lemma_truths_append s bc eq j (Replay.elaborate s ds doc).P.assertions (DS.closures s dds)

let lemma_extension_root (u:TR.uninterpreted) (larger:bool) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (choice:E.hilbert_choice (TR.carrier u) s) (doc:P.document) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (extension larger s bc eq choice doc other)) =
  let ds = Replay.context s doc in
  let dds = dependent_context larger s doc ds in
  Root.lemma_root_build u s bc eq choice ds other;
  Root.lemma_root_dbuild u s bc eq choice dds (E.build s bc eq choice ds other)

let lemma_extension_expansion (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (
    let ds = Replay.context s doc in
    extension false s bc eq choice doc other ==
      DS.build s bc eq choice (SP.dependent_context s doc ds)
        (E.build s bc eq choice ds other)) =
  ()

let lemma_extension_expansion_dependent (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
  (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (
    let ds = Replay.context s doc in
    extension true s bc eq choice doc other ==
      DS.build s bc eq choice (DReplay.context s doc ds)
        (E.build s bc eq choice ds other)) =
  ()

let lemma_extension_real (#base:sort -> Type0) (larger:bool) (s:S.checked_schema) (bc:S.boolean_carrier base)
                         (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                         (doc:P.document) (other:V.interpretation base (S.signature s))
                         (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
          (ensures RL.real_laws s bc eq (extension larger s bc eq choice doc other) reals) =
  let ds = Replay.context s doc in
  RX.lemma_build_real s bc eq choice ds other reals;
  RX.lemma_dbuild_real s bc eq choice (dependent_context larger s doc ds) (E.build s bc eq choice ds other) reals

let lemma_extension_real_model (#base:sort -> Type0) (larger:bool) (s:S.checked_schema) (bc:S.boolean_carrier base)
                               (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                               (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (requires RL.real_model s bc eq other)
          (ensures RL.real_model s bc eq (extension larger s bc eq choice doc other)) =
  FStar.Classical.exists_elim (RL.real_model s bc eq (extension larger s bc eq choice doc other))
    #(RL.carrier base) #(fun reals -> RL.real_laws s bc eq other reals) ()
    (fun reals -> lemma_extension_real larger s bc eq choice doc other reals)

let lemma_extension_division (#base:sort -> Type0) (larger:bool) (s:S.checked_schema) (bc:S.boolean_carrier base)
                             (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                             (doc:P.document) (other:V.interpretation base (S.signature s))
  : Lemma (requires DV.division_laws s bc eq other)
          (ensures DV.division_laws s bc eq (extension larger s bc eq choice doc other)) =
  let ds = Replay.context s doc in
  DX.lemma_build_division s bc eq choice ds other;
  DX.lemma_dbuild_division s bc eq choice (dependent_context larger s doc ds) (E.build s bc eq choice ds other)

let lemma_check_with (#base:sort -> Type0) (larger:bool) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires check_with larger s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    DV.division_laws s bc eq other)
          (ensures not (T.truths s bc eq other doc.P.assertions)) =
  if T.truths s bc eq other doc.P.assertions then (
    let j = extension larger s bc eq choice doc other in
    lemma_extension larger s bc eq choice doc other;
    SP.lemma_full_forall_elimination s bc j;
    if RL.real_primitive s then lemma_extension_real_model larger s bc eq choice doc other;
    lemma_extension_division larger s bc eq choice doc other;
    if SP.needs_real_semantics s (elaborate_with larger s doc).P.entries then
      SP.lemma_needs_real_primitive s (elaborate_with larger s doc).P.entries;
    SP.lemma_check_document s bc eq j (elaborate_with larger s doc))

let lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires check s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    DV.division_laws s bc eq other)
          (ensures not (T.truths s bc eq other doc.P.assertions)) =
  lemma_check_with false s bc eq choice other doc

let lemma_check_dependent (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                          (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                          (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires check_dependent s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    DV.division_laws s bc eq other)
          (ensures not (T.truths s bc eq other doc.P.assertions)) =
  lemma_check_with true s bc eq choice other doc

let lemma_check_binder (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:T.scalar_model base) (choice:E.hilbert_choice base s)
                       (other:V.interpretation base (S.signature s)) (doc:P.document)
  : Lemma (requires check_binder s doc == Some 0 /\
                    Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    DV.division_laws s bc eq other)
          (ensures not (T.truths s bc eq other doc.P.assertions)) =
  if T.truths s bc eq other doc.P.assertions then (
    let j = extension true s bc eq choice doc other in
    let expanded = elaborate_dependent s doc in
    let augmented = elaborate_binder s doc in
    lemma_extension true s bc eq choice doc other;
    SP.lemma_full_forall_elimination s bc j;
    if RL.real_primitive s then lemma_extension_real_model true s bc eq choice doc other;
    lemma_extension_division true s bc eq choice doc other;
    Binder.lemma_equations s bc eq j expanded;
    SP.lemma_truths_append s bc eq j expanded.P.assertions (Binder.equations s expanded);
    if SP.needs_real_semantics s augmented.P.entries then
      SP.lemma_needs_real_primitive s augmented.P.entries;
    SP.lemma_check_document s bc eq j augmented)
