module Z3IndependentExistentialDer

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module E = Z3SortedSkolem
module D = Z3ExprScope

val check (q e:expr) : bool

val lemma_check (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
                (q e:expr)
  : Lemma (requires E.exists_model s bc other /\ D.scoped [] q /\ D.scoped [] e /\ check q e)
          (ensures T.evaluate s bc eq other q == T.evaluate s bc eq other e)
