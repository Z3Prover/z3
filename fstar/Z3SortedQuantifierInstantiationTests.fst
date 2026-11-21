module Z3SortedQuantifierInstantiationTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module K = Z3SortedQuantifierInstantiation
module D = Z3ExprScope
module C = Z3CanonicalOps
module R = Z3ClauseSyntax
module Syntax = Z3QuantifierInstantiationSyntax

let body =
  Quantifier Forall_k [bool_sort] bool_sort (R.mk_eq_expr (Var 1 bool_sort) (Var 0 bool_sort))
let instantiated =
  Quantifier Forall_k [bool_sort] bool_sort (R.mk_eq_expr R.true_expr (Var 0 bool_sort))
let quantified = Quantifier Forall_k [bool_sort] bool_sort body
let formula = App (C.or_decl 2) [App C.not_decl [quantified]; instantiated]
let malformed = App (C.or_decl 0) [App C.not_decl [quantified]; instantiated]

let nested_instance (#base:sort -> Type0) (s:S.checked_schema)
                    (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                    (other:V.interpretation base (S.signature s))
  : Lemma (requires Q.forall_elimination_model s bc other)
          (ensures D.scoped [] formula /\ Syntax.check [R.true_expr] formula /\
                   T.truth s bc eq other formula) =
  assert_norm (D.scoped [] formula /\ Syntax.check [R.true_expr] formula);
  K.lemma_check s bc eq other [R.true_expr] formula

let malformed_preserves_legacy_acceptance ()
  : Lemma (Syntax.check [R.true_expr] malformed /\ not (D.scoped [] malformed)) =
  assert_norm (Syntax.check [R.true_expr] malformed /\ not (D.scoped [] malformed))
