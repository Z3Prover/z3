module Z3SortedCommutativityTests

open Z3AstTheory
open Z3OperatorTags
module D = Z3ExprScope
module C = Z3CommutativitySyntax
module R = Z3ClauseSyntax
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module SC = Z3SortedCommutativity

let int_s = SortApp IntSymbol []
let scope = [int_s; int_s; bool_sort; bool_sort]
let binary (name:string) (tag:int) (t:sort) : func_decl =
  { decl_name = name; domain = [t; t]; range = t; interp = Some tag; int_params = [] }
let plus = binary "+" op_plus int_s
let mul = binary "*" op_mul int_s
let conj = binary "and" op_and bool_sort
let disj = binary "or" op_or bool_sort
let ix = Var 0 int_s
let iy = Var 1 int_s
let bx = Var 2 bool_sort
let bz = Var 3 bool_sort

let sorted_commutativity (#base:sort -> Type0) (s:S.checked_schema)
                         (bc:S.boolean_carrier base) (model:T.scalar_model base)
                         (other:V.interpretation base (S.signature s))
                         (rho:V.environment base (S.signature s) scope)
  : Lemma (
      let a = App plus [ix; iy] in
      let b = App plus [iy; ix] in
      assert_norm (D.scoped scope a /\ D.scoped scope b /\
                   D.scoped scope (App mul [ix; iy]) /\ D.scoped scope (App mul [iy; ix]) /\
                   D.scoped scope (App conj [bx; bz]) /\ D.scoped scope (App conj [bz; bx]) /\
                   D.scoped scope (App disj [bx; bz]) /\ D.scoped scope (App disj [bz; bx]) /\
                   D.scoped scope (App (R.eq_decl int_s) [ix; iy]) /\
                   D.scoped scope (App (R.eq_decl int_s) [iy; ix]));
      T.evaluate_at s bc model other scope rho a == T.evaluate_at s bc model other scope rho b /\
      T.evaluate_at s bc model other scope rho (App mul [ix; iy]) ==
        T.evaluate_at s bc model other scope rho (App mul [iy; ix]) /\
      T.evaluate_at s bc model other scope rho (App conj [bx; bz]) ==
        T.evaluate_at s bc model other scope rho (App conj [bz; bx]) /\
      T.evaluate_at s bc model other scope rho (App disj [bx; bz]) ==
        T.evaluate_at s bc model other scope rho (App disj [bz; bx]) /\
      T.evaluate_at s bc model other scope rho (App (R.eq_decl int_s) [ix; iy]) ==
        T.evaluate_at s bc model other scope rho (App (R.eq_decl int_s) [iy; ix])) =
  let a = App plus [ix; iy] in
  let b = App plus [iy; ix] in
  assert_norm (D.scoped scope a /\ D.scoped scope b /\ C.commutativity_step a b);
  SC.lemma_step s bc model other scope rho a b;
  assert_norm (D.scoped scope (App mul [ix; iy]) /\ D.scoped scope (App mul [iy; ix]) /\
               C.commutativity_step (App mul [ix; iy]) (App mul [iy; ix]) /\
               D.scoped scope (App conj [bx; bz]) /\ D.scoped scope (App conj [bz; bx]) /\
               C.commutativity_step (App conj [bx; bz]) (App conj [bz; bx]) /\
               D.scoped scope (App disj [bx; bz]) /\ D.scoped scope (App disj [bz; bx]) /\
               C.commutativity_step (App disj [bx; bz]) (App disj [bz; bx]) /\
               D.scoped scope (App (R.eq_decl int_s) [ix; iy]) /\
               D.scoped scope (App (R.eq_decl int_s) [iy; ix]) /\
               C.commutativity_step (App (R.eq_decl int_s) [ix; iy]) (App (R.eq_decl int_s) [iy; ix]));
  SC.lemma_step s bc model other scope rho (App mul [ix; iy]) (App mul [iy; ix]);
  SC.lemma_step s bc model other scope rho (App conj [bx; bz]) (App conj [bz; bx]);
  SC.lemma_step s bc model other scope rho (App disj [bx; bz]) (App disj [bz; bx]);
  SC.lemma_step s bc model other scope rho (App (R.eq_decl int_s) [ix; iy]) (App (R.eq_decl int_s) [iy; ix])
