module Z3IndependentDefinitionRoot

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module Context = Z3IndependentDefinitionContext

val lemma_build_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (items:list (Context.item s inputs)) (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (Context.build s bc eq inputs items other))
