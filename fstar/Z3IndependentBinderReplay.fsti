module Z3IndependentBinderReplay

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module U = Z3UnifiedProofSyntax
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module RL = Z3SortedReal
module NR = Z3NnfReplay
module BS = Z3BinderScopeIndependent

val replay (real:bool) (assertions:list expr) (c:U.binder_certificate)
           (concl:U.judgment) : NR.verdict

val lemma_replay (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
  (eq:T.scalar_model base) (other:V.interpretation base (S.signature s))
  (real:bool) (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    (real ==> RL.real_model s bc eq other) /\
                    T.truths s bc eq other assertions /\ replay real assertions c concl == NR.Replayed)
          (ensures BS.binder_judgment_scoped [] concl /\
                   NR.holds_at s bc eq other [] (T.empty_environment (S.signature s)) concl)
