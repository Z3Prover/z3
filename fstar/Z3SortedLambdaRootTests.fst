module Z3SortedLambdaRootTests

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module S = Z3DatatypeSignature
module K = Z3SortedLambda
module E = Z3SortedLambdaEquality
module R = Z3TypedRoot
module SR = Z3SortedRoot
module T = Z3SortedSemantics
module Q = Z3SortedQuantifier
module D = Z3ExprScope
module Syntax = Z3LambdaSyntax
module Tests = Z3SortedLambdaTests
module ET = Z3SortedLambdaEqualityTests
module C = Z3ClauseSyntax
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let rec lemma_append_arguments (#base:sort -> Type0) (sigma:V.signature)
                               (ss ts:list sort) (vs:V.arguments base sigma ss)
                               (ws:V.arguments base sigma ts)
  : Lemma (R.append_arguments sigma ss ts vs ws == vs @ ws)
          (decreases ss) =
  match ss, vs with
  | _ :: rest, _ :: tail -> lemma_append_arguments sigma rest ts tail ws
  | _, _ -> ()

let rec lemma_reverse_arguments (#base:sort -> Type0) (sigma:V.signature)
                                (ss:list sort) (vs:V.arguments base sigma ss)
  : Lemma (R.reverse_arguments sigma ss vs == K.reverse_arguments sigma ss vs)
          (decreases ss) =
  match ss, vs with
  | s :: rest, v :: tail ->
    lemma_reverse_arguments sigma rest tail;
    lemma_append_arguments sigma (L.rev rest) [s] (R.reverse_arguments sigma rest tail) [v];
    LP.rev_rev' (s :: rest);
    LP.rev_rev' rest;
    LP.rev_rev' (v :: tail);
    LP.rev_rev' tail
  | _, _ -> ()

let supported (sigma:V.signature) (bound:list sort) (element:sort) : bool =
  R.free sigma (ArraySort bound element)

let lemma_select_case (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
                      (bound:list sort) (element:sort{supported (S.signature sch) bound element})
                      (body:R.body_of u sch bound element) (vs:R.targuments u sch bound)
  : Lemma (requires R.root_model u sch i)
          (ensures not (L.mem (K.select_decl bound element) (S.signature sch)) /\
                   i.V.application (K.select_decl bound element)
                     (i.V.quantification Lambda_k bound element body :: vs) ==
                   body (K.reverse_arguments (S.signature sch) bound vs)) =
  R.lemma_not_constructor sch (K.select_decl bound element);
  lemma_reverse_arguments (S.signature sch) bound vs;
  R.law_select_lambda i bound element body vs

let lemma_select_model (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
  : Lemma (requires R.root_model u sch i)
          (ensures K.select_model (S.signature sch) (supported (S.signature sch)) i) =
  let at (bound:list sort) (element:sort{supported (S.signature sch) bound element})
         (body:R.body_of u sch bound element) (vs:R.targuments u sch bound)
    : Lemma (not (L.mem (K.select_decl bound element) (S.signature sch)) /\
             i.V.application (K.select_decl bound element)
               (i.V.quantification Lambda_k bound element body :: vs) ==
             body (K.reverse_arguments (S.signature sch) bound vs)) =
    lemma_select_case u sch i bound element body vs in
  FStar.Classical.forall_intro_4 at

let direct_beta_supported (sigma:V.signature) (e:expr) : bool =
  match e with
  | App _ (Quantifier Lambda_k bound _ body :: _) ->
    supported sigma bound (get_sort body)
  | _ -> false

let lemma_direct_beta (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
                     (scope:list sort) (rho:V.environment (R.carrier u) (S.signature sch) scope)
                     (e result:expr)
  : Lemma (requires R.root_model u sch i /\ direct_beta_supported (S.signature sch) e /\
                    D.scoped scope e /\ Syntax.beta e == Some result)
          (ensures D.scoped scope result /\ get_sort e == get_sort result /\
                   V.evaluate (S.signature sch) i scope rho e ==
                   V.evaluate (S.signature sch) i scope rho result) =
  lemma_select_model u sch i;
  K.lemma_beta (S.signature sch) (supported (S.signature sch)) i scope rho e result

let lemma_standard_select_model (u:R.uninterpreted) (sch:S.checked_schema)
                                (uf:R.symbols u sch)
  : Lemma (K.select_model (S.signature sch) (supported (S.signature sch)) (R.standard u sch uf)) =
  R.lemma_standard_root u sch uf;
  lemma_select_model u sch (R.standard u sch uf)

unfold let constant_apply (u:R.uninterpreted) (sch:S.checked_schema) (uf:R.symbols u sch)
                   (f:func_decl) (xs:R.targuments u sch f.domain)
  : GTot (R.tvalue u sch f.range) =
  match f.range with
  | ArraySort bound element ->
    if bound <> [] && supported (S.signature sch) bound element && f = K.constant_decl bound element then
      (match xs with
       | [v] ->
         (R.standard u sch uf).V.quantification Lambda_k bound element
           (K.constant_body (S.signature sch) bound element v)
       | _ -> FStar.Pervasives.false_elim ())
    else uf.R.apply f xs
  | _ -> uf.R.apply f xs

unfold let constant_symbols (u:R.uninterpreted) (sch:S.checked_schema) (uf:R.symbols u sch)
  : R.symbols u sch = {
  apply = constant_apply u sch uf;
  lambda = uf.R.lambda;
}

let lemma_constant_case (u:R.uninterpreted) (sch:S.checked_schema) (uf:R.symbols u sch)
                        (bound:list sort{bound <> []})
                        (element:sort{supported (S.signature sch) bound element})
                        (v:R.tvalue u sch element)
  : Lemma (
      let i = R.standard u sch (constant_symbols u sch uf) in
      not (L.mem (K.constant_decl bound element) (S.signature sch)) /\
      i.V.application (K.constant_decl bound element) [v] ==
      i.V.quantification Lambda_k bound element (K.constant_body (S.signature sch) bound element v)) =
  let new_uf = constant_symbols u sch uf in
  let f = K.constant_decl bound element in
  R.lemma_not_constructor sch f;
  R.lemma_standard_application u sch new_uf f [v];
  assert (R.classify (S.signature sch) f == R.Other);
  assert (R.interpreted u sch f [v] == None);
  assert (R.theory_application u sch new_uf f [v] == new_uf.R.apply f [v]);
  assert (f = K.constant_decl bound element);
  assert (f.range == ArraySort bound element);
  assert (bound <> [] && supported (S.signature sch) bound element &&
          f = K.constant_decl bound element);
  assert (constant_apply u sch uf f [v] ==
          (R.standard u sch uf).V.quantification Lambda_k bound element
            (K.constant_body (S.signature sch) bound element v));
  assert (new_uf.R.apply f [v] ==
          (R.standard u sch uf).V.quantification Lambda_k bound element
            (K.constant_body (S.signature sch) bound element v));
  assert ((R.standard u sch new_uf).V.quantification Lambda_k bound element
            (K.constant_body (S.signature sch) bound element v) ==
          (R.standard u sch uf).V.quantification Lambda_k bound element
            (K.constant_body (S.signature sch) bound element v))

let lemma_constant_model (u:R.uninterpreted) (sch:S.checked_schema) (uf:R.symbols u sch)
  : Lemma (K.constant_model (S.signature sch) (supported (S.signature sch))
             (R.standard u sch (constant_symbols u sch uf))) =
  let at (bound:list sort{bound <> []})
         (element:sort{supported (S.signature sch) bound element})
         (v:R.tvalue u sch element)
    : Lemma (
        let i = R.standard u sch (constant_symbols u sch uf) in
        not (L.mem (K.constant_decl bound element) (S.signature sch)) /\
        i.V.application (K.constant_decl bound element) [v] ==
        i.V.quantification Lambda_k bound element (K.constant_body (S.signature sch) bound element v)) =
    lemma_constant_case u sch uf bound element v in
  FStar.Classical.forall_intro_3 at

let lemma_sorted_constant_case (u:R.uninterpreted) (sch:S.checked_schema) (uf:R.symbols u sch)
                               (bound:list sort{bound <> []})
                               (element:sort{supported (S.signature sch) bound element})
                               (v:R.tvalue u sch element)
  : Lemma (
      let i = R.standard u sch (constant_symbols u sch uf) in
      let sorted = T.interpretation sch (R.booleans u) (SR.root_scalars u) i in
      not (L.mem (K.constant_decl bound element) (S.signature sch)) /\
      sorted.V.application (K.constant_decl bound element) [v] ==
      sorted.V.quantification Lambda_k bound element (K.constant_body (S.signature sch) bound element v)) =
  let i = R.standard u sch (constant_symbols u sch uf) in
  R.lemma_standard_root u sch (constant_symbols u sch uf);
  lemma_constant_case u sch uf bound element v;
  SR.lemma_application_agreement u sch i (K.constant_decl bound element) [v]

let lemma_sorted_constant_model (u:R.uninterpreted) (sch:S.checked_schema) (uf:R.symbols u sch)
  : Lemma (K.constant_model (S.signature sch) (supported (S.signature sch))
             (T.interpretation sch (R.booleans u) (SR.root_scalars u)
               (R.standard u sch (constant_symbols u sch uf)))) =
  let at (bound:list sort{bound <> []})
         (element:sort{supported (S.signature sch) bound element})
         (v:R.tvalue u sch element)
    : Lemma (
        let i = R.standard u sch (constant_symbols u sch uf) in
        let sorted = T.interpretation sch (R.booleans u) (SR.root_scalars u) i in
        not (L.mem (K.constant_decl bound element) (S.signature sch)) /\
        sorted.V.application (K.constant_decl bound element) [v] ==
        sorted.V.quantification Lambda_k bound element (K.constant_body (S.signature sch) bound element v)) =
    lemma_sorted_constant_case u sch uf bound element v in
  FStar.Classical.forall_intro_3 at

let lemma_extensional_case (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
                           (bound:list sort) (element:sort{supported (S.signature sch) bound element})
                           (left right:R.body_of u sch bound element)
  : Lemma (requires R.root_model u sch i)
          (ensures E.extensional_case (S.signature sch) i bound element left right) =
  let sigma = S.signature sch in
  let a = i.V.quantification Lambda_k bound element left in
  let b = i.V.quantification Lambda_k bound element right in
  if a == b then (
    let pointwise (vs:V.arguments (R.carrier u) sigma (L.rev bound))
      : Lemma (left vs == right vs) =
      LP.rev_involutive bound;
      let ix = K.reverse_arguments sigma (L.rev bound) vs in
      lemma_reverse_arguments sigma bound ix;
      LP.rev_involutive vs;
      R.law_select_lambda i bound element left ix;
      R.law_select_lambda i bound element right ix in
    FStar.Classical.forall_intro pointwise);
  if (forall (vs:V.arguments (R.carrier u) sigma (L.rev bound)). left vs == right vs) then (
    let pointwise (ix:V.arguments (R.carrier u) sigma bound)
      : Lemma (i.V.application (R.select_decl bound element) (a :: ix) ==
               i.V.application (R.select_decl bound element) (b :: ix)) =
      R.law_select_lambda i bound element left ix;
      R.law_select_lambda i bound element right ix in
    FStar.Classical.forall_intro pointwise;
    R.law_array_extensionality i bound element a b)

let lemma_extensional_model (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
  : Lemma (requires R.root_model u sch i)
          (ensures E.extensional_model (S.signature sch) (supported (S.signature sch)) i) =
  let at (bound:list sort) (element:sort{supported (S.signature sch) bound element})
         (left right:R.body_of u sch bound element)
    : Lemma (E.extensional_case (S.signature sch) i bound element left right) =
    lemma_extensional_case u sch i bound element left right in
  FStar.Classical.forall_intro_4 at

let lemma_sorted_extensional_model (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
  : Lemma (requires R.root_model u sch i)
          (ensures E.extensional_model (S.signature sch) (supported (S.signature sch))
                     (T.interpretation sch (R.booleans u) (SR.root_scalars u) i)) =
  let sorted = T.interpretation sch (R.booleans u) (SR.root_scalars u) i in
  let at (bound:list sort) (element:sort{supported (S.signature sch) bound element})
         (left right:R.body_of u sch bound element)
    : Lemma (E.extensional_case (S.signature sch) sorted bound element left right) =
    lemma_extensional_case u sch i bound element left right;
    assert (sorted.V.quantification == i.V.quantification) in
  FStar.Classical.forall_intro_4 at

let lemma_forall_case (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
                      (bound:list sort) (body:Q.ghost_body (R.carrier u) sch bound)
  : Lemma (requires R.root_model u sch i)
          (ensures Q.forall_case sch (R.booleans u) i bound body) =
  assert (R.forall_case u sch i bound body);
  SR.lemma_truth_value sch (i.V.quantification Forall_k bound bool_sort body);
  let pointwise (vs:R.targuments u sch (L.rev bound))
    : Lemma (T.truth_value sch (R.booleans u) (body vs) == R.truth sch (body vs)) =
    SR.lemma_truth_value sch (body vs) in
  FStar.Classical.forall_intro pointwise

let lemma_forall_model (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
  : Lemma (requires R.root_model u sch i)
          (ensures Q.forall_model sch (R.booleans u) i) =
  introduce forall (bound:list sort) (body:Q.ghost_body (R.carrier u) sch bound).
    Q.forall_case sch (R.booleans u) i bound body
  with lemma_forall_case u sch i bound body

let direct_views (e:expr) : bool =
  match e with
  | App _ [Quantifier Lambda_k _ _ _; Quantifier Lambda_k _ _ _] -> true
  | _ -> false

let lemma_direct_extensional (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
                             (scope:list sort)
                             (rho:V.environment (R.carrier u) (S.signature sch) scope)
                             (e result:expr)
  : Lemma (requires R.root_model u sch i /\ direct_views e /\
                    E.supported_extensional (supported (S.signature sch)) e /\
                    D.scoped scope e /\ Syntax.extensional e == Some result)
          (ensures D.scoped scope result /\ get_sort result == bool_sort /\
                   T.truth_at sch (R.booleans u) (SR.root_scalars u) i scope rho e ==
                   T.truth_at sch (R.booleans u) (SR.root_scalars u) i scope rho result) =
  lemma_forall_model u sch i;
  lemma_sorted_extensional_model u sch i;
  E.lemma_extensional sch (R.booleans u) (SR.root_scalars u) i
    (supported (S.signature sch)) scope rho e result

let heterogeneous_beta_in_root (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
                               (rho:V.environment (R.carrier u) (S.signature sch)
                                 [Tests.integer; bool_sort; Tests.outer])
  : Lemma (requires R.root_model u sch i /\
                    supported (S.signature sch) Tests.bound (ArraySort [Tests.inner] Tests.outer))
          (ensures D.scoped [Tests.integer; bool_sort; Tests.outer] Tests.beta_input /\
                   D.scoped [Tests.integer; bool_sort; Tests.outer] Tests.beta_result /\
                   V.evaluate (S.signature sch) i [Tests.integer; bool_sort; Tests.outer] rho Tests.beta_input ==
                   V.evaluate (S.signature sch) i [Tests.integer; bool_sort; Tests.outer] rho Tests.beta_result) =
  assert_norm (D.scoped [Tests.integer; bool_sort; Tests.outer] Tests.beta_input /\
               Syntax.beta Tests.beta_input == Some Tests.beta_result);
  lemma_direct_beta u sch i [Tests.integer; bool_sort; Tests.outer] rho
    Tests.beta_input Tests.beta_result

let other_nested_lambda =
  Quantifier Lambda_k [Tests.inner] (ArraySort [Tests.inner] Tests.outer)
    (App { Tests.combine with decl_name = "lambda-other" }
      [Var 2 Tests.integer; Var 1 bool_sort; Var 5 Tests.outer])
let other_lambda =
  Quantifier Lambda_k Tests.bound (ArraySort Tests.bound (ArraySort [Tests.inner] Tests.outer))
    other_nested_lambda
let equality_input = C.mk_eq_expr Tests.beta_lambda other_lambda
let equality_result =
  Quantifier Forall_k Tests.bound bool_sort (C.mk_eq_expr Tests.nested_lambda other_nested_lambda)

let heterogeneous_extensional_in_root (u:R.uninterpreted) (sch:S.checked_schema) (i:R.interp u sch)
                                      (rho:V.environment (R.carrier u) (S.signature sch)
                                        [Tests.integer; bool_sort; Tests.outer])
  : Lemma (requires R.root_model u sch i /\
                    supported (S.signature sch) Tests.bound (ArraySort [Tests.inner] Tests.outer))
          (ensures D.scoped [Tests.integer; bool_sort; Tests.outer] equality_input /\
                   D.scoped [Tests.integer; bool_sort; Tests.outer] equality_result /\
                   T.truth_at sch (R.booleans u) (SR.root_scalars u) i
                     [Tests.integer; bool_sort; Tests.outer] rho equality_input ==
                   T.truth_at sch (R.booleans u) (SR.root_scalars u) i
                     [Tests.integer; bool_sort; Tests.outer] rho equality_result) =
  assert_norm (D.scoped [Tests.integer; bool_sort; Tests.outer] equality_input /\
               Syntax.extensional equality_input == Some equality_result);
  lemma_direct_extensional u sch i [Tests.integer; bool_sort; Tests.outer] rho
    equality_input equality_result

let constant_beta_in_standard (u:R.uninterpreted) (sch:S.checked_schema) (uf:R.symbols u sch)
                              (rho:V.environment (R.carrier u) (S.signature sch)
                                [Tests.outer; Tests.integer; bool_sort])
  : Lemma (requires supported (S.signature sch) Tests.bound Tests.outer)
          (ensures D.scoped [Tests.outer; Tests.integer; bool_sort] Tests.constant_beta /\
                   V.evaluate (S.signature sch) (R.standard u sch (constant_symbols u sch uf))
                     [Tests.outer; Tests.integer; bool_sort] rho Tests.constant_beta ==
                   V.evaluate (S.signature sch) (R.standard u sch (constant_symbols u sch uf))
                     [Tests.outer; Tests.integer; bool_sort] rho (Var 0 Tests.outer)) =
  let i = R.standard u sch (constant_symbols u sch uf) in
  R.lemma_standard_root u sch (constant_symbols u sch uf);
  lemma_select_model u sch i;
  lemma_constant_model u sch uf;
  Tests.nested_array_constant_beta (S.signature sch) (supported (S.signature sch)) i rho

let constant_extensional_in_standard (u:R.uninterpreted) (sch:S.checked_schema) (uf:R.symbols u sch)
                                     (rho:V.environment (R.carrier u) (S.signature sch) [Tests.outer])
  : Lemma (requires supported (S.signature sch) Tests.bound Tests.outer)
          (ensures D.scoped [Tests.outer] ET.input /\ D.scoped [Tests.outer] ET.result /\
                   T.truth_at sch (R.booleans u) (SR.root_scalars u)
                     (R.standard u sch (constant_symbols u sch uf)) [Tests.outer] rho ET.input ==
                   T.truth_at sch (R.booleans u) (SR.root_scalars u)
                     (R.standard u sch (constant_symbols u sch uf)) [Tests.outer] rho ET.result) =
  let i = R.standard u sch (constant_symbols u sch uf) in
  R.lemma_standard_root u sch (constant_symbols u sch uf);
  lemma_forall_model u sch i;
  lemma_sorted_extensional_model u sch i;
  lemma_sorted_constant_model u sch uf;
  ET.constant_and_lambda_views sch (R.booleans u) (SR.root_scalars u) i
    (supported (S.signature sch)) rho
