module Z3QuantifierInstantiationSyntaxTests

open Z3AstTheory
module Syntax = Z3QuantifierInstantiationSyntax
module C = Z3CanonicalOps
module R = Z3ClauseSyntax
module D = Z3ExprScope

let forall_boolean = Quantifier Forall_k [bool_sort] bool_sort (Var 0 bool_sort)
let valid = App (C.or_decl 2) [App C.not_decl [forall_boolean]; R.true_expr]
let malformed = App (C.or_decl 0) [App C.not_decl [forall_boolean]; R.true_expr]

let native_acceptance_and_scope_boundary ()
  : Lemma (Syntax.check [R.true_expr] valid /\
           Syntax.check [R.true_expr] malformed /\ not (D.scoped [] malformed) /\
           not (Syntax.check [] valid) /\
           not (Syntax.check [R.false_expr] valid) /\
           not (Syntax.check [Var 0 bool_sort] valid)) =
  assert_norm (Syntax.check [R.true_expr] valid /\
               Syntax.check [R.true_expr] malformed /\ not (D.scoped [] malformed) /\
               not (Syntax.check [] valid) /\
               not (Syntax.check [R.false_expr] valid) /\
               not (Syntax.check [Var 0 bool_sort] valid))
