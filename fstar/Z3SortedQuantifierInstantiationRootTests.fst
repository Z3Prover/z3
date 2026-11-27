module Z3SortedQuantifierInstantiationRootTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module R = Z3TypedRoot
module SR = Z3SortedRoot
module Tests = Z3SortedQuantifierInstantiationTests
module L = FStar.List.Tot

let lemma_elimination_case (u:R.uninterpreted) (s:S.checked_schema) (i:R.interp u s)
                           (bound:list sort) (body:Q.ghost_body (R.carrier u) s bound)
                           (vs:V.arguments (R.carrier u) (S.signature s) (L.rev bound))
  : Lemma (requires R.root_model u s i)
          (ensures Q.elimination_case s (R.booleans u) i bound body vs) =
  assert (R.forall_case u s i bound body);
  SR.lemma_truth_value s (i.V.quantification Forall_k bound bool_sort body);
  SR.lemma_truth_value s (body vs)

let lemma_elimination_model (u:R.uninterpreted) (s:S.checked_schema) (i:R.interp u s)
  : Lemma (requires R.root_model u s i)
          (ensures Q.forall_elimination_model s (R.booleans u) i) =
  let at (bound:list sort) (body:Q.ghost_body (R.carrier u) s bound)
         (vs:V.arguments (R.carrier u) (S.signature s) (L.rev bound))
    : Lemma (Q.elimination_case s (R.booleans u) i bound body vs) =
    lemma_elimination_case u s i bound body vs in
  FStar.Classical.forall_intro_3 at

let nested_instance_in_root (u:R.uninterpreted) (s:S.checked_schema) (i:R.interp u s)
  : Lemma (requires R.root_model u s i)
          (ensures T.truth s (R.booleans u) (SR.root_scalars u) i Tests.formula) =
  lemma_elimination_model u s i;
  Tests.nested_instance s (R.booleans u) (SR.root_scalars u) i
