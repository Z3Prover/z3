module Z3IndependentDefinitionContext

open Z3AstTheory
open FStar.List.Tot
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module Model = Z3IndependentDefinitionModel
module RL = Z3SortedReal
module DV = Z3SortedIntDivision
module L = FStar.List.Tot

type item (s:S.checked_schema) (inputs:list expr) = {
  formula: expr;
  definition: Model.definition s inputs formula;
}

let rec safe (s:S.checked_schema) (inputs:list expr)
             (newer:item s inputs) (older:list (item s inputs))
  : Tot bool (decreases older) =
  match older with
  | [] -> true
  | d :: rest -> D.fresh [newer.definition] d.formula && safe s inputs newer rest

let rec ordered (s:S.checked_schema) (inputs:list expr) (items:list (item s inputs))
  : Tot bool (decreases items) =
  match items with
  | [] -> true
  | d :: rest -> safe s inputs d rest && ordered s inputs rest

let rec insert_at (s:S.checked_schema) (inputs:list expr) (position:nat)
  (candidate:item s inputs) (items:list (item s inputs))
  : Tot (list (item s inputs)) (decreases position) =
  if position = 0 then candidate :: items
  else match items with
  | [] -> [candidate]
  | current :: rest ->
    current :: insert_at s inputs (position - 1) candidate rest

let rec insertion_position (s:S.checked_schema) (inputs:list expr)
  (candidate:item s inputs) (items:list (item s inputs))
  (index minimum maximum preferred:nat)
  : Tot (option nat) (decreases items) =
  match items with
  | [] ->
    if minimum <= maximum then
      Some (if preferred < minimum then minimum
            else if maximum < preferred then maximum
            else preferred)
    else None
  | current :: rest ->
    let minimum' =
      if not (D.fresh [candidate.definition] current.formula)
      then index + 1 else minimum in
    let maximum' =
      if not (D.fresh [current.definition] candidate.formula) && index < maximum
      then index else maximum in
    insertion_position s inputs candidate rest (index + 1)
      minimum' maximum' preferred

let rec dependency_insert (s:S.checked_schema) (inputs:list expr)
  (remaining:list (item s inputs)) (ordered_items:list (item s inputs))
  : Tot (result:option (list (item s inputs)){
      match result with
      | None -> true
      | Some items -> ordered s inputs items})
    (decreases remaining) =
  match remaining with
  | [] -> if ordered s inputs ordered_items then Some ordered_items else None
  | candidate :: rest ->
    let count = L.length ordered_items in
    match insertion_position s inputs candidate ordered_items 0 0 count count with
    | None -> None
    | Some position ->
      dependency_insert s inputs rest
        (insert_at s inputs position candidate ordered_items)

let dependency_order (s:S.checked_schema) (inputs:list expr)
  (items:list (item s inputs))
  : result:option (list (item s inputs)){
      match result with
      | None -> true
      | Some ordered_items -> ordered s inputs ordered_items} =
  if ordered s inputs items then Some items
  else dependency_insert s inputs items []

let rec formulas (s:S.checked_schema) (inputs:list expr) (items:list (item s inputs))
  : Tot (list expr) (decreases items) =
  match items with [] -> [] | d :: rest -> d.formula :: formulas s inputs rest

val build (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : GTot (V.interpretation base (S.signature s))

val lemma_build_nil (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (other:V.interpretation base (S.signature s))
  : Lemma (build s bc eq inputs [] other == other)

val lemma_build_cons (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (d:item s inputs) (rest:list (item s inputs))
  (other:V.interpretation base (S.signature s))
  : Lemma (build s bc eq inputs (d :: rest) other ==
    Model.override s bc eq (build s bc eq inputs rest other)
      inputs d.formula d.definition)

val lemma_build_inputs (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (ensures T.truths s bc eq (build s bc eq inputs items other) inputs ==
                   T.truths s bc eq other inputs)

val lemma_build_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (ensures (Q.forall_model s bc (build s bc eq inputs items other) <==>
                    Q.forall_model s bc other) /\
                   (E.exists_model s bc (build s bc eq inputs items other) <==>
                    E.exists_model s bc other))

val lemma_build_real (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
    (ensures RL.real_laws s bc eq (build s bc eq inputs items other) reals)

val lemma_build_division (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (requires DV.division_laws s bc eq other)
    (ensures DV.division_laws s bc eq (build s bc eq inputs items other))

val lemma_build_context (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base) (inputs:list expr)
  (items:list (item s inputs)) (other:V.interpretation base (S.signature s))
  : Lemma (requires ordered s inputs items /\ Q.forall_model s bc other)
    (ensures T.truths s bc eq (build s bc eq inputs items other) (formulas s inputs items))
