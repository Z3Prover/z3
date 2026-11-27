module Z3IndependentIntegerSplitReplay

open Z3AstTheory
module G = Z3LpGomorySyntax
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

val check (c:G.certificate) (conclusion:expr) (facts:list expr) : bool

val lemma_check (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (c:G.certificate) (conclusion:expr) (facts:list expr)
  : Lemma (requires check c conclusion facts /\ T.truths s bc model other facts)
          (ensures T.truth s bc model other conclusion)
