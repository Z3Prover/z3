module Z3IndependentFiniteFieldRoot

module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module TR = Z3TypedRoot
module FF = Z3SortedFiniteField
module D = Z3ExprScope
module R = Z3ClauseSyntax
module Replay = Z3IndependentFiniteFieldReplay

val project (u:TR.uninterpreted) (p:int{p > 1})
  (v:V.tree (TR.carrier u)) : Tot int

val lemma_project_range (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1}) (v:V.tree (TR.carrier u))
  : Lemma (requires not (V.datatype_sort (S.signature sch) (FF.ff_sort p)) /\
                    V.has_sort (S.signature sch) (FF.ff_sort p) v)
          (ensures 0 <= project u p v /\ project u p v < p)

val lemma_project_reflection (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1}) (x y:V.tree (TR.carrier u))
  : Lemma (requires not (V.datatype_sort (S.signature sch) (FF.ff_sort p)) /\
                    V.has_sort (S.signature sch) (FF.ff_sort p) x /\
                    V.has_sort (S.signature sch) (FF.ff_sort p) y)
          (ensures (x == y <==> project u p x == project u p y))

val model (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (other:TR.interp u sch) : GTot (FF.model (TR.carrier u) sch p)

val field_symbols (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) : GTot (TR.symbols u sch)

val lemma_root_inhabited (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch)
  : Lemma (TR.root_model u sch (TR.standard u sch (field_symbols u sch p uf)))

val lemma_preserves_other (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (f:Z3AstTheory.func_decl)
  (xs:TR.targuments u sch f.domain)
  : Lemma (requires (match FF.numeral (Z3AstTheory.App f []) with Some (q, _) -> q <> p | None -> True) /\
                    (match FF.operation_of f with Some (q, _) -> q <> p | None -> True))
          (ensures (field_symbols u sch p uf).TR.apply f xs == (TR.standard u sch uf).V.application f xs)

val lemma_override_application (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (f:Z3AstTheory.func_decl)
  (xs:TR.targuments u sch f.domain)
  : Lemma (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    (FF.override sch p (model u sch p root)).V.application f xs ==
    root.V.application f xs)

val lemma_sorted_application (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (f:Z3AstTheory.func_decl)
  (xs:TR.targuments u sch f.domain)
  : Lemma (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    Z3SortedSemantics.application sch (TR.booleans u) (Z3SortedRoot.root_scalars u)
      (FF.override sch p (model u sch p root)) f xs ==
    root.V.application f xs)

val lemma_sorted_evaluate (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (scope:list Z3AstTheory.sort)
  (rho:V.environment (TR.carrier u) (S.signature sch) scope)
  (e:Z3AstTheory.expr{D.scoped scope e})
  : Lemma (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    Z3SortedSemantics.evaluate_at sch (TR.booleans u) (Z3SortedRoot.root_scalars u)
      (FF.override sch p (model u sch p root)) scope rho e ==
    V.evaluate (S.signature sch) root scope rho e)

val lemma_truth_agreement (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (e:Z3AstTheory.expr)
  : Lemma (
    let root = TR.standard u sch (field_symbols u sch p uf) in
    Z3SortedSemantics.truth sch (TR.booleans u) (Z3SortedRoot.root_scalars u)
      (FF.override sch p (model u sch p root)) e ==
    Z3SortedSemantics.truth sch (TR.booleans u) (Z3SortedRoot.root_scalars u) root e)

val lemma_rewrite (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (a b:Z3AstTheory.expr)
  : Lemma (requires Replay.rewrite p a b)
          (ensures Z3SortedSemantics.truth sch (TR.booleans u) (Z3SortedRoot.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) (R.mk_eq_expr a b))

val lemma_clause (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (e:Z3AstTheory.expr)
  : Lemma (requires Replay.clause p e)
          (ensures Z3SortedSemantics.truth sch (TR.booleans u) (Z3SortedRoot.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) e)

val lemma_pac (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (c:FF.certificate) (e:Z3AstTheory.expr)
  : Lemma (requires Replay.pac p c e)
          (ensures Z3SortedSemantics.truth sch (TR.booleans u) (Z3SortedRoot.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) e)

val lemma_pac_with_evidence (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{p > 1 /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (c:FF.certificate) (e:Z3AstTheory.expr)
  (evidence:option (int & list int))
  : Lemma (requires Replay.pac_with_evidence p c e evidence)
          (ensures Z3SortedSemantics.truth sch (TR.booleans u) (Z3SortedRoot.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) e)

val lemma_pac_for_prime (u:TR.uninterpreted) (sch:S.checked_schema)
  (p:int{FStar.Math.Euclid.is_prime p /\ not (V.datatype_sort (S.signature sch) (FF.ff_sort p))})
  (uf:TR.symbols u sch) (c:FF.certificate) (e:Z3AstTheory.expr)
  : Lemma (requires Replay.pac_for_prime p c e)
          (ensures Z3SortedSemantics.truth sch (TR.booleans u) (Z3SortedRoot.root_scalars u)
            (TR.standard u sch (field_symbols u sch p uf)) e)
