module Z3SortedBooleanRewriteTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module R = Z3ClauseSyntax
module X = Z3BooleanRewriteSyntax
module K = Z3SortedBooleanRewrite
module B = Z3BoundedBoolEquiv

let p = Var 0 bool_sort
let q = Var 1 bool_sort
let disjunction = App (R.or_decl [p; q]) [p; q]
let de_morgan =
  let np = R.mk_not_expr p in
  let nq = R.mk_not_expr q in
  App (R.and_decl [np; nq]) [np; nq]

let equivalence_covers_scoped_demorgan (#base:sort -> Type0) (s:S.checked_schema)
                                      (bc:S.boolean_carrier base) (core:T.scalar_model base)
                                      (other:V.interpretation base (S.signature s))
                                      (rho:V.environment base (S.signature s) [bool_sort; bool_sort])
  : Lemma (T.truth_at s bc core other [bool_sort; bool_sort] rho (R.mk_not_expr disjunction) ==
           T.truth_at s bc core other [bool_sort; bool_sort] rho de_morgan) =
  assert_norm (X.boolean_equiv 3 0 (R.mk_not_expr disjunction) de_morgan);
  assert_norm (Z3ExprScope.scoped [bool_sort; bool_sort] (R.mk_not_expr disjunction));
  assert_norm (Z3ExprScope.scoped [bool_sort; bool_sort] de_morgan);
  K.lemma_equivalent s bc core other [bool_sort; bool_sort] rho 3 0
    (R.mk_not_expr disjunction) de_morgan

let search_covers_scoped_demorgan (#base:sort -> Type0) (s:S.checked_schema)
                                 (bc:S.boolean_carrier base) (core:T.scalar_model base)
                                 (other:V.interpretation base (S.signature s))
                                 (rho:V.environment base (S.signature s) [bool_sort; bool_sort])
  : Lemma (T.truth_at s bc core other [bool_sort; bool_sort] rho (R.mk_not_expr disjunction) ==
           T.truth_at s bc core other [bool_sort; bool_sort] rho de_morgan) =
  assert_norm (X.boolean_search (R.mk_not_expr disjunction) de_morgan);
  assert_norm (Z3ExprScope.scoped [bool_sort; bool_sort] (R.mk_not_expr disjunction));
  assert_norm (Z3ExprScope.scoped [bool_sort; bool_sort] de_morgan);
  K.lemma_search s bc core other [bool_sort; bool_sort] rho
    (R.mk_not_expr disjunction) de_morgan

let reflexive_equality_precedes_boundary_and_zero_depth ()
  : Lemma (let nested = ArraySort [(SortApp IntSymbol [])]
                         (ArraySort [bool_sort] (SortApp RealSymbol [])) in
           let a = Var 0 nested in
           let e = R.mk_eq_expr a a in
           X.boolean_cut [e] 0 e == B.Bool true) =
  assert_norm (
    let nested = ArraySort [(SortApp IntSymbol [])]
                   (ArraySort [bool_sort] (SortApp RealSymbol [])) in
    let a = Var 0 nested in
    let e = R.mk_eq_expr a a in
    X.boolean_cut [e] 0 e == B.Bool true)

let malformed_xor_stays_opaque ()
  : Lemma (let f = { X.boolean_xor_decl with int_params = [1] } in
           X.boolean_cut [] 3 (App f [p; q]) == B.Atom (App f [p; q])) =
  assert_norm (
    let f = { X.boolean_xor_decl with int_params = [1] } in
    X.boolean_cut [] 3 (App f [p; q]) == B.Atom (App f [p; q]))

let flatten_preserves_order_duplicates_and_values (#base:sort -> Type0) (s:S.checked_schema)
                                                 (bc:S.boolean_carrier base) (core:T.scalar_model base)
                                                 (other:V.interpretation base (S.signature s))
                                                 (rho:V.environment base (S.signature s) [bool_sort; bool_sort])
  : Lemma (
      let nested = App (R.and_decl [q; p]) [q; p] in
      let before = App (R.and_decl [p; nested]) [p; nested] in
      let after = App (R.and_decl [p; q; p]) [p; q; p] in
      X.flatten_rewrite before == Some after /\
      T.truth_at s bc core other [bool_sort; bool_sort] rho before ==
      T.truth_at s bc core other [bool_sort; bool_sort] rho after) =
  let nested = App (R.and_decl [q; p]) [q; p] in
  let before = App (R.and_decl [p; nested]) [p; nested] in
  let after = App (R.and_decl [p; q; p]) [p; q; p] in
  assert_norm (X.flatten_rewrite before == Some after);
  assert_norm (Z3ExprScope.scoped [bool_sort; bool_sort] before);
  assert_norm (Z3ExprScope.scoped [bool_sort; bool_sort] after);
  K.lemma_flatten_rewrite s bc core other [bool_sort; bool_sort] rho before after
