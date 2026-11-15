module Z3IndependentDefinitionNnf

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module NR = Z3NnfReplay
module SP = Z3SortedProof
module Scope = Z3ExprScope
module Context = Z3IndependentDefinitionContext
module CE = Z3IndependentDefinitionContextEquivalence

let rec bounded_items (s:S.checked_schema) (inputs:list expr)
  (items:list (Context.item s inputs)) (remaining:nat)
  : Tot bool (decreases items) =
  match items with
  | [] -> true
  | item :: rest ->
    if remaining = 0 then false
    else if None? (expression_budget 1024 item.Context.definition.D.body) then false
    else bounded_items s inputs rest (remaining - 1)

let candidate (s:S.checked_schema) (inputs:list expr) (items:list (Context.item s inputs))
  (entry:P.entry) : option U.judgment =
  if entry.P.premise_ids <> [] then None
  else if None? (expression_budget 1024 entry.P.formula) then None
  else if not (bounded_items s inputs items 16) then None
  else match entry.P.rule, U.classify_fact entry.P.formula with
  | U.QuantifierIntroduction c, Some (U.Equal a b)
  | U.QuantifierIntroduction c, Some (U.Observational a b) ->
    if NR.nnf_root c && Scope.scoped [] a && Scope.scoped [] b &&
       SP.boolean_expression s (SP.proposition (U.Equal a b)) &&
       CE.matches s inputs items 64 a b
    then U.classify_fact entry.P.formula else None
  | _, _ -> None

val lemma_candidate (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (items:list (Context.item s inputs))
  (entry:P.entry) (j:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\
      T.truths s bc eq other (Context.formulas s inputs items) /\
      candidate s inputs items entry == Some j)
    (ensures T.truth s bc eq other (SP.proposition j))
