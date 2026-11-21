module Z3IndependentIntQuotientClause

open Z3AstTheory
module D = Z3ExprScope
module DV = Z3SortedIntDivision
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

val check (conclusion:expr) : bool

val lemma_check (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s)) (conclusion:expr)
  : Lemma (requires DV.division_laws s bc model other /\
                    D.scoped [] conclusion /\ get_sort conclusion == bool_sort /\
                    check conclusion)
          (ensures T.truth s bc model other conclusion)
