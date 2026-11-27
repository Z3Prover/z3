module Z3IndependentIntBounds

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module D = Z3ExprScope

val check (equation bounds:expr) : bool

val lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (model:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (equation bounds:expr)
  : Lemma (requires D.scoped [] equation /\ D.scoped [] bounds /\ check equation bounds)
          (ensures T.truth s bc model other equation == T.truth s bc model other bounds)
