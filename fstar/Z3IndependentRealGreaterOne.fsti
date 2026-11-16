module Z3IndependentRealGreaterOne

open Z3AstTheory
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue
module RL = Z3SortedReal

val check (s:S.checked_schema) (facts:list expr) : bool

val lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
  (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
  (reals:RL.carrier base) (facts:list expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ T.truths s bc model other facts /\
                    check s facts)
          (ensures False)
