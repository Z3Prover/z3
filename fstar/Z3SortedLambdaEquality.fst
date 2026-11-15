module Z3SortedLambdaEquality

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module D = Z3ExprScope
module K = Z3SortedLambda
module Syntax = Z3LambdaSyntax
module C = Z3ClauseSyntax
module L = FStar.List.Tot

let extensional_case (#base:sort -> Type0) (sigma:V.signature)
                     (i:V.interpretation base sigma) (bound:list sort) (element:sort)
                     (left right:V.arguments base sigma (L.rev bound) -> GTot (V.value base sigma element))
  : prop =
  i.quantification Lambda_k bound element left == i.quantification Lambda_k bound element right
  <==> (forall (vs:V.arguments base sigma (L.rev bound)). left vs == right vs)

let extensional_model (#base:sort -> Type0) (sigma:V.signature)
                      (supports:list sort -> sort -> bool)
                      (i:V.interpretation base sigma) : prop =
  forall (bound:list sort) (element:sort{supports bound element})
         (left right:V.arguments base sigma (L.rev bound) -> GTot (V.value base sigma element)).
    extensional_case sigma i bound element left right

let supported_extensional (supports:list sort -> sort -> bool) (e:expr) : bool =
  match e with
  | App _ [a; _] ->
    (match Syntax.lambda_view a with
     | Some (bound, body) -> supports bound (get_sort body)
     | None -> false)
  | _ -> false

let view_models (#base:sort -> Type0) (sigma:V.signature)
                (supports:list sort -> sort -> bool)
                (i:V.interpretation base sigma) (e:expr) : prop =
  match e with
  | App _ [a; b] -> K.view_model sigma supports i a /\ K.view_model sigma supports i b
  | _ -> True

let lemma_extensional (#base:sort -> Type0) (s:S.checked_schema)
                      (bc:S.boolean_carrier base) (eq:T.scalar_model base)
                      (other:V.interpretation base (S.signature s))
                      (supports:list sort -> sort -> bool)
                      (scope:list sort) (rho:V.environment base (S.signature s) scope)
                      (e result:expr)
  : Lemma (requires
      Q.forall_model s bc other /\
      extensional_model (S.signature s) supports (T.interpretation s bc eq other) /\
      view_models (S.signature s) supports (T.interpretation s bc eq other) e /\
      supported_extensional supports e /\
      D.scoped scope e /\ Syntax.extensional e == Some result)
    (ensures D.scoped scope result /\ get_sort result == bool_sort /\
             T.truth_at s bc eq other scope rho e == T.truth_at s bc eq other scope rho result) =
  let sigma = S.signature s in
  let i = T.interpretation s bc eq other in
  match e with
  | App _ [a; b] ->
    (match Syntax.lambda_view a, Syntax.lambda_view b with
     | Some (bound, left), Some (bound', right) ->
       K.lemma_lambda_view sigma supports i scope rho a bound left;
       K.lemma_lambda_view sigma supports i scope rho b bound' right;
       T.lemma_equality_at s bc eq other scope rho a b;
       Q.lemma_forall_truth s bc eq other scope rho bound (C.mk_eq_expr left right);
       let lb = V.typed_body sigma bound (get_sort left)
         (V.evaluate_body sigma i scope rho bound left) in
       let rb = V.typed_body sigma bound (get_sort right)
         (V.evaluate_body sigma i scope rho bound right) in
       let pointwise (vs:V.arguments base sigma (L.rev bound))
         : Lemma (
             T.truth_at s bc eq other (L.rev bound @ scope)
               (V.extend sigma scope (L.rev bound) vs rho) (C.mk_eq_expr left right) <==>
             lb vs == rb vs) =
         T.lemma_equality_at s bc eq other (L.rev bound @ scope)
           (V.extend sigma scope (L.rev bound) vs rho) left right in
       FStar.Classical.forall_intro pointwise;
       assert (extensional_case sigma i bound (get_sort left) lb rb);
       assert (i.quantification Lambda_k bound (get_sort left) lb ==
               i.quantification Lambda_k bound (get_sort right) rb <==>
               (forall (vs:V.arguments base sigma (L.rev bound)). lb vs == rb vs))
     | _, _ -> ())
  | _ -> ()
