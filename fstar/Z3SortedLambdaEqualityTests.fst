module Z3SortedLambdaEqualityTests

open Z3AstTheory
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module D = Z3ExprScope
module K = Z3SortedLambda
module E = Z3SortedLambdaEquality
module Syntax = Z3LambdaSyntax
module C = Z3ClauseSyntax
module Tests = Z3SortedLambdaTests

let input = C.mk_eq_expr Tests.constant Tests.expanded
let result =
  Quantifier Forall_k Tests.bound bool_sort (C.mk_eq_expr Tests.body Tests.body)

let constant_and_lambda_views (#base:sort -> Type0) (s:S.checked_schema)
                              (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                              (other:V.interpretation base (S.signature s))
                              (supports:list sort -> sort -> bool)
                              (rho:V.environment base (S.signature s) [Tests.outer])
  : Lemma (requires Q.forall_model s bc other /\
                    K.constant_model (S.signature s) supports (T.interpretation s bc eq other) /\
                    E.extensional_model (S.signature s) supports (T.interpretation s bc eq other) /\
                    supports Tests.bound Tests.outer)
          (ensures D.scoped [Tests.outer] input /\ D.scoped [Tests.outer] result /\
                   T.truth_at s bc eq other [Tests.outer] rho input ==
                   T.truth_at s bc eq other [Tests.outer] rho result) =
  assert_norm (D.scoped [Tests.outer] input /\ Syntax.extensional input == Some result);
  E.lemma_extensional s bc eq other supports [Tests.outer] rho input result
