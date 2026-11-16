module Z3IndependentConditionalDefinition

open Z3AstTheory
module A = Z3ArraySyntax
module B = Z3BoundedBoolEquiv
module D = Z3ExprScope
module R = Z3ClauseSyntax
module S = Z3DatatypeSignature
module SA = Z3SortedArray
module T = Z3SortedSemantics
module V = Z3DatatypeValue

let lemma_directional (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (premise choice name:expr)
  : Lemma (requires T.truth s bc model other premise /\ directional premise choice name)
          (ensures T.truth s bc model other (R.mk_eq_expr choice name)) =
  match A.ite_parts choice with
  | None -> ()
  | Some (c, t, u) ->
    let neg = R.mk_not_expr c in
    let positive = R.mk_eq_expr name t in
    let negative = R.mk_eq_expr name u in
    let a = disjunction neg positive in
    let b = disjunction c negative in
    let rho = T.empty_environment (S.signature s) in
    SA.lemma_ite_scope [] choice c t u;
    T.lemma_nary s bc model other (R.and_decl [a; b]) [a; b] B.And;
    T.lemma_nary s bc model other (R.or_decl [neg; positive]) [neg; positive] B.Or;
    T.lemma_nary s bc model other (R.or_decl [c; negative]) [c; negative] B.Or;
    T.lemma_negation s bc model other R.not_decl c;
    T.lemma_equality s bc model other name t;
    T.lemma_equality s bc model other name u;
    SA.lemma_ite s bc model other [] rho choice c t u;
    T.lemma_equality s bc model other choice name

let lemma_check (#base:sort -> Type0) (s:S.checked_schema)
  (bc:S.boolean_carrier base) (model:T.scalar_model base)
  (other:V.interpretation base (S.signature s))
  (premise left right:expr)
  : Lemma (requires T.truth s bc model other premise /\ check premise left right)
          (ensures T.truth s bc model other (R.mk_eq_expr left right)) =
  if directional premise left right then
    lemma_directional s bc model other premise left right
  else (
    lemma_directional s bc model other premise right left;
    T.lemma_equality s bc model other right left;
    T.lemma_equality s bc model other left right)
