module Z3IndependentGroundDefinitionRoot

open Z3AstTheory
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module TR = Z3TypedRoot
module Ground = Z3IndependentGroundDefinition
module A = Z3SortedArray

val lemma_override_root (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (formula:expr) (d:Ground.definition s inputs formula)
  (other:TR.interp u s)
  : Lemma (requires TR.root_model u s other)
    (ensures TR.root_model u s (Ground.override s bc eq other inputs formula d))

val lemma_override_array_model (u:TR.uninterpreted) (s:S.checked_schema)
  (bc:S.boolean_carrier (TR.carrier u)) (eq:T.scalar_model (TR.carrier u))
  (inputs:list expr) (formula:expr) (d:Ground.definition s inputs formula)
  (other:TR.interp u s) (family:A.family (TR.carrier u) (S.signature s))
  : Lemma (requires A.model s bc eq other family)
    (ensures A.model s bc eq (Ground.override s bc eq other inputs formula d) family)
