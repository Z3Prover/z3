module Z3IndependentFiniteFieldReplay

open Z3AstTheory
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module FF = Z3SortedFiniteField
module R = Z3ClauseSyntax
module E = FStar.Math.Euclid

val rewrite (p:int) (a b:expr) : bool
val clause (p:int) (e:expr) : bool
val pac_with_evidence (p:int) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int)) : bool
val pac_for_prime (p:int{E.is_prime p}) (c:FF.certificate) (e:expr) : bool
val pac (p:int) (c:FF.certificate) (e:expr) : bool

val lemma_rewrite (#base:sort -> Type0) (s:S.checked_schema) (p:pos)
  (m:FF.model base s p) (a b:expr)
  : Lemma (requires rewrite p a b)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) (R.mk_eq_expr a b))

val lemma_clause (#base:sort -> Type0) (s:S.checked_schema) (p:pos)
  (m:FF.model base s p) (e:expr)
  : Lemma (requires clause p e)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) e)

val lemma_pac_with_evidence (#base:sort -> Type0) (s:S.checked_schema) (p:pos)
  (m:FF.model base s p) (c:FF.certificate) (e:expr)
  (evidence:option (int & list int))
  : Lemma (requires pac_with_evidence p c e evidence)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) e)

val lemma_pac_for_prime (#base:sort -> Type0) (s:S.checked_schema) (p:int{E.is_prime p})
  (m:FF.model base s p) (c:FF.certificate) (e:expr)
  : Lemma (requires pac_for_prime p c e)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) e)

val lemma_pac (#base:sort -> Type0) (s:S.checked_schema) (p:pos)
  (m:FF.model base s p) (c:FF.certificate) (e:expr)
  : Lemma (requires pac p c e)
          (ensures T.truth s m.FF.booleans m.FF.scalar_model (FF.override s p m) e)
