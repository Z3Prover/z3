module Z3IndependentDefinitionNnf

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module P = Z3DocumentSyntax
module U = Z3UnifiedProofSyntax
module SP = Z3SortedProof
module Context = Z3IndependentDefinitionContext
module CE = Z3IndependentDefinitionContextEquivalence

let lemma_candidate (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (items:list (Context.item s inputs))
  (entry:P.entry) (j:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\
      T.truths s bc eq other (Context.formulas s inputs items) /\
      candidate s inputs items entry == Some j)
    (ensures T.truth s bc eq other (SP.proposition j)) =
  match j with
  | U.Equal a b ->
    CE.lemma_matches s bc eq other inputs items [] (T.empty_environment (S.signature s)) 64 a b;
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_same_value s bc eq other a b;
    T.lemma_equality s bc eq other a b
  | U.Observational a b ->
    CE.lemma_matches s bc eq other inputs items [] (T.empty_environment (S.signature s)) 64 a b;
    V.lemma_sort_eq (get_sort b) (get_sort a);
    T.lemma_values_observations_at s bc eq other [] (T.empty_environment (S.signature s)) a b;
    SP.lemma_observational_proposition s bc eq other a b
  | U.Holds _ -> ()
