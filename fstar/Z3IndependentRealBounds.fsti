module Z3IndependentRealBounds

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module D = Z3ExprScope
module RL = Z3SortedReal

val check (equation bounds:expr) : bool

val lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (reals:RL.carrier base) (equation bounds:expr)
  : Lemma (requires RL.real_laws s bc model other reals /\ D.scoped [] equation /\
                    D.scoped [] bounds /\ check equation bounds)
          (ensures T.truth s bc model other equation == T.truth s bc model other bounds)
