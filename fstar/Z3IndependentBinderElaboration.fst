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
module NR = Z3NnfReplay
module Binder = Z3IndependentBinderReplay
module SP = Z3SortedProof
module L = FStar.List.Tot

let candidate (s:S.checked_schema) (assertions:list expr) (entry:P.entry) : option U.judgment =
  if entry.P.premise_ids <> [] then None
  else match entry.P.rule, U.classify_fact entry.P.formula with
  | U.QuantifierIntroduction c, Some j ->
    if SP.boolean_expression s (SP.proposition j) &&
       NR.replay_with (RL.real_primitive s) assertions c j = NR.Unreplayed &&
       Binder.replay (RL.real_primitive s) assertions c j = NR.Replayed
    then Some j else None
  | _, _ -> None

let rec collect (s:S.checked_schema) (assertions:list expr)
                (entries:list P.entry) (equations:list expr) (acc selected:list P.entry)
  : Tot (list expr & (list P.entry & list P.entry)) (decreases entries) =
  match entries with
  | [] -> equations, (L.rev acc, selected)
  | e :: rest ->
    (match candidate s assertions e with
     | Some j ->
       collect s assertions rest (SP.proposition j :: equations) ({ e with P.rule = U.Asserted } :: acc)
         (e :: selected)
     | None -> collect s assertions rest equations (e :: acc) selected)

let equations (s:S.checked_schema) (doc:P.document) : list expr =
  fst (collect s doc.P.assertions doc.P.entries [] [] [])

let augment (s:S.checked_schema) (doc:P.document) : P.document =
  let additions, (entries, _) = collect s doc.P.assertions doc.P.entries [] [] [] in
  { doc with P.assertions = doc.P.assertions @ additions; P.entries = entries }

let augment_with_selection (s:S.checked_schema) (doc:P.document) : P.document & list P.entry =
  let additions, (entries, selected) = collect s doc.P.assertions doc.P.entries [] [] [] in
  ({ doc with P.assertions = doc.P.assertions @ additions; P.entries = entries }, selected)

let rec lemma_collect_selection (s:S.checked_schema) (assertions:list expr)
                                (entries:list P.entry) (equations:list expr)
                                (acc selected:list P.entry) (entry:P.entry)
  : Lemma (ensures L.mem entry (snd (snd (collect s assertions entries equations acc selected))) <==>
                   L.mem entry selected \/
                   (L.mem entry entries /\ Some? (candidate s assertions entry)))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    (match candidate s assertions e with
     | None -> lemma_collect_selection s assertions rest equations (e :: acc) selected entry
     | Some j ->
       lemma_collect_selection s assertions rest (SP.proposition j :: equations)
         ({ e with P.rule = U.Asserted } :: acc) (e :: selected) entry)

let lemma_selection (s:S.checked_schema) (doc:P.document) (entry:P.entry)
  : Lemma (ensures L.mem entry (snd (augment_with_selection s doc)) <==>
                   L.mem entry doc.P.entries /\ Some? (candidate s doc.P.assertions entry)) =
  lemma_collect_selection s doc.P.assertions doc.P.entries [] [] [] entry

let rec reference_equations (s:S.checked_schema) (assertions:list expr)
                            (entries:list P.entry) (acc:list expr)
  : GTot (list expr) (decreases entries) =
  match entries with
  | [] -> acc
  | e :: rest ->
    let next = match candidate s assertions e with
      | Some j -> SP.proposition j :: acc
      | None -> acc in
    reference_equations s assertions rest next

let rec reference_entries (s:S.checked_schema) (assertions:list expr)
                          (entries acc:list P.entry)
  : GTot (list P.entry) (decreases entries) =
  match entries with
  | [] -> acc
  | e :: rest ->
    let e' = if Some? (candidate s assertions e) then { e with P.rule = U.Asserted } else e in
    reference_entries s assertions rest (e' :: acc)

let rec lemma_collect_reference (s:S.checked_schema) (assertions:list expr)
                                (entries:list P.entry) (equations:list expr) (acc selected:list P.entry)
  : Lemma (ensures fst (collect s assertions entries equations acc selected) ==
                     reference_equations s assertions entries equations /\
                   fst (snd (collect s assertions entries equations acc selected)) ==
                     L.rev (reference_entries s assertions entries acc))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    (match candidate s assertions e with
     | None -> lemma_collect_reference s assertions rest equations (e :: acc) selected
     | Some j -> lemma_collect_reference s assertions rest (SP.proposition j :: equations)
                   ({ e with P.rule = U.Asserted } :: acc) (e :: selected))

let lemma_candidate (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (assertions:list expr) (entry:P.entry) (j:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other assertions /\ candidate s assertions entry == Some j)
          (ensures T.truth s bc eq other (SP.proposition j)) =
  match entry.P.rule with
  | U.QuantifierIntroduction c ->
    Binder.lemma_replay s bc eq other (RL.real_primitive s) assertions c j;
    (match j with
     | U.Equal a b ->
       V.lemma_sort_eq (get_sort b) (get_sort a);
       T.lemma_same_value s bc eq other a b;
       T.lemma_equality s bc eq other a b
     | U.Observational a b ->
       V.lemma_sort_eq (get_sort b) (get_sort a);
       T.lemma_same_value s bc eq other a b;
       T.lemma_values_observations_at s bc eq other [] (T.empty_environment (S.signature s)) a b;
       SP.lemma_observational_proposition s bc eq other a b
     | U.Holds _ -> ())
  | _ -> ()

let rec lemma_equations_acc (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                            (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                            (assertions:list expr) (entries:list P.entry) (acc:list expr)
                            (entry_acc selected:list P.entry)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other assertions /\ T.truths s bc eq other acc)
          (ensures T.truths s bc eq other (fst (collect s assertions entries acc entry_acc selected)))
          (decreases entries) =
  match entries with
  | [] -> ()
  | e :: rest ->
    (match candidate s assertions e with
     | None -> lemma_equations_acc s bc eq other assertions rest acc (e :: entry_acc) selected
     | Some j ->
       lemma_candidate s bc eq other assertions e j;
       lemma_equations_acc s bc eq other assertions rest (SP.proposition j :: acc)
         ({ e with P.rule = U.Asserted } :: entry_acc) (e :: selected))

let lemma_equations (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                    (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                    (doc:P.document)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (RL.real_primitive s ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other doc.P.assertions)
          (ensures T.truths s bc eq other (equations s doc)) =
  lemma_equations_acc s bc eq other doc.P.assertions doc.P.entries [] [] []
