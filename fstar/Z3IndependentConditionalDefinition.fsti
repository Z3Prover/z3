module Z3IndependentConditionalDefinition

open Z3AstTheory
module A = Z3ArraySyntax
module D = Z3ExprScope
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let conjunction (a b:expr) : expr = App (R.and_decl [a; b]) [a; b]
let disjunction (a b:expr) : expr = App (R.or_decl [a; b]) [a; b]

let directional (premise choice name:expr) : bool =
  D.scoped [] premise && D.scoped [] choice && D.scoped [] name &&
  (match A.ite_parts choice with
  | Some (c, t, u) ->
    get_sort name = get_sort t &&
    premise = conjunction
      (disjunction (R.mk_not_expr c) (R.mk_eq_expr name t))
      (disjunction c (R.mk_eq_expr name u))
  | None -> false)

let check (premise left right:expr) : bool =
  directional premise left right || directional premise right left

val lemma_check (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (premise left right:expr)
  : Lemma (requires T.truth s bc model other premise /\ check premise left right)
          (ensures T.truth s bc model other (R.mk_eq_expr left right))
