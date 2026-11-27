module Z3IndependentDefinitionModel

open Z3AstTheory
module S = Z3DatatypeSignature
module D = Z3DefinitionSyntax
module V = Z3DatatypeValue
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module Pair = Z3IndependentDefinitionPair
module Scope = Z3ExprScope
module RL = Z3SortedReal
module DV = Z3SortedIntDivision

type definition (s:S.checked_schema) (inputs:list expr) (formula:expr) =
  d:D.definition{Pair.valid s inputs formula d}

val override (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : V.interpretation base (S.signature s)

val lemma_override_application (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (f:func_decl) (args:V.arguments base (S.signature s) f.domain)
  : Lemma (requires f <> d.D.symbol)
    (ensures (override s bc eq other inputs formula d).V.application f args ==
             other.V.application f args)

val lemma_override_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma ((override s bc eq other inputs formula d).V.quantification ==
           other.V.quantification)

val lemma_fresh (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (scope:list sort) (rho:V.environment base (S.signature s) scope) (e:expr)
  : Lemma (requires Scope.scoped scope e /\ D.fresh [d] e)
    (ensures T.evaluate_at s bc eq other scope rho e ==
             T.evaluate_at s bc eq (override s bc eq other inputs formula d) scope rho e)

val lemma_inputs (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (ensures T.truths s bc eq (override s bc eq other inputs formula d) inputs ==
                   T.truths s bc eq other inputs)

val lemma_quantification (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (ensures (Q.forall_model s bc (override s bc eq other inputs formula d) <==>
                    Q.forall_model s bc other) /\
                   (E.exists_model s bc (override s bc eq other inputs formula d) <==>
                    E.exists_model s bc other))

val lemma_real (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  (reals:RL.carrier base)
  : Lemma (requires RL.real_laws s bc eq other reals)
    (ensures RL.real_laws s bc eq (override s bc eq other inputs formula d) reals)

val lemma_division (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (requires DV.division_laws s bc eq other)
    (ensures DV.division_laws s bc eq (override s bc eq other inputs formula d))

val lemma_pointwise (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (t:sort) (d:definition s inputs formula)
  (rho:V.environment base (S.signature s) [t])
  : Lemma (requires d.D.symbol.domain == [t])
    (ensures T.truth_at s bc eq (override s bc eq other inputs formula d) [t] rho
                    (App d.D.symbol [Var 0 t]) <==>
             T.truth_at s bc eq (override s bc eq other inputs formula d) [t] rho d.D.body)

val lemma_definition (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (eq:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (inputs:list expr) (formula:expr) (d:definition s inputs formula)
  : Lemma (requires Q.forall_model s bc other)
    (ensures T.truth s bc eq (override s bc eq other inputs formula d) formula)
