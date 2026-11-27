module Z3SortedLambda

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module D = Z3ExprScope
module K = Z3SortedBinding
module Syntax = Z3LambdaSyntax
module Sub = Z3Substitution
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module FE = FStar.FunctionalExtensionality

let rec lemma_reverse_sorts (args acc:list expr) (ss sacc:list sort)
  : Lemma (requires sorts_match args ss /\ sorts_match acc sacc)
          (ensures sorts_match (L.rev_acc args acc) (L.rev_acc ss sacc))
          (decreases args) =
  match args, ss with
  | a :: rest, s :: tail -> lemma_reverse_sorts rest (a :: acc) tail (s :: sacc)
  | _, _ -> ()

let rec lemma_reverse_fields (#base:sort -> Type0) (sigma:V.signature)
                             (ss sacc:list sort) (vs acc:list (V.tree base))
  : Lemma (requires V.fields_have_sorts sigma ss vs /\ V.fields_have_sorts sigma sacc acc)
          (ensures V.fields_have_sorts sigma (L.rev_acc ss sacc) (L.rev_acc vs acc))
          (decreases ss) =
  match ss, vs with
  | s :: rest, v :: tail -> lemma_reverse_fields sigma rest (s :: sacc) tail (v :: acc)
  | _, _ -> ()

let reverse_arguments (#base:sort -> Type0) (sigma:V.signature) (ss:list sort)
                      (vs:V.arguments base sigma ss)
  : Tot (V.arguments base sigma (L.rev ss)) =
  lemma_reverse_fields sigma ss [] vs [];
  L.rev vs

let rec lemma_evaluate_reverse_acc (#base:sort -> Type0) (sigma:V.signature)
                                   (i:V.interpretation base sigma) (scope:list sort)
                                   (rho:V.environment base sigma scope)
                                   (args acc:list expr) (ss sacc:list sort)
  : Lemma (requires D.scoped_args scope args /\ D.scoped_args scope acc /\
                    sorts_match args ss /\ sorts_match acc sacc)
          (ensures
            D.scoped_args scope (L.rev_acc args acc) /\
            sorts_match (L.rev_acc args acc) (L.rev_acc ss sacc) /\
            V.evaluate_args sigma i scope rho (L.rev_acc args acc) (L.rev_acc ss sacc) ==
            L.rev_acc (V.evaluate_args sigma i scope rho args ss)
                      (V.evaluate_args sigma i scope rho acc sacc))
          (decreases args) =
  D.lemma_scoped_reverse_acc scope args acc;
  lemma_reverse_sorts args acc ss sacc;
  match args, ss with
  | e :: rest, s :: tail ->
    V.lemma_sort_eq (get_sort e) s;
    lemma_evaluate_reverse_acc sigma i scope rho rest (e :: acc) tail (s :: sacc)
  | _, _ -> ()

let constant_decl (bound:list sort) (element:sort) : func_decl = {
  decl_name = "const"; domain = [element]; range = ArraySort bound element;
  interp = Some Z3OperatorTags.op_const_array; int_params = [];
}

let select_decl (bound:list sort) (element:sort) : func_decl = {
  decl_name = "select"; domain = ArraySort bound element :: bound; range = element;
  interp = Some Z3OperatorTags.op_select; int_params = [];
}

let select_model (#base:sort -> Type0) (sigma:V.signature)
                 (supports:list sort -> sort -> bool)
                 (i:V.interpretation base sigma) : prop =
  forall (bound:list sort) (element:sort{supports bound element})
         (body:V.arguments base sigma (L.rev bound) -> GTot (V.value base sigma element))
         (vs:V.arguments base sigma bound).
    not (L.mem (select_decl bound element) sigma) /\
    i.application (select_decl bound element)
      (i.quantification Lambda_k bound element body :: vs) ==
    body (reverse_arguments sigma bound vs)

let constant_body (#base:sort -> Type0) (sigma:V.signature)
                  (bound:list sort) (element:sort) (v:V.value base sigma element)
  : V.arguments base sigma (L.rev bound) -> GTot (V.value base sigma element) =
  V.typed_body sigma bound element
    (FE.on_dom_g (V.arguments base sigma (L.rev bound)) (fun _ -> (v <: V.tree base)))

let lemma_constant_body (#base:sort -> Type0) (sigma:V.signature)
                        (bound:list sort) (element:sort) (v:V.value base sigma element)
  : Lemma (constant_body sigma bound element v ==
           V.typed_body sigma bound element
             (FE.on_dom_g (V.arguments base sigma (L.rev bound)) (fun _ -> (v <: V.tree base)))) =
  assert_norm (constant_body sigma bound element v ==
               V.typed_body sigma bound element
                 (FE.on_dom_g (V.arguments base sigma (L.rev bound)) (fun _ -> (v <: V.tree base))))

let constant_model (#base:sort -> Type0) (sigma:V.signature)
                   (supports:list sort -> sort -> bool)
                   (i:V.interpretation base sigma) : prop =
  forall (bound:list sort{bound <> []}) (element:sort{supports bound element})
         (v:V.value base sigma element).
    not (L.mem (constant_decl bound element) sigma) /\
    i.application (constant_decl bound element) [v] ==
    i.quantification Lambda_k bound element (constant_body sigma bound element v)

let view_model (#base:sort -> Type0) (sigma:V.signature)
               (supports:list sort -> sort -> bool)
               (i:V.interpretation base sigma) (e:expr) : prop =
  match e with
  | App _ _ -> constant_model sigma supports i
  | _ -> True

let supported_beta (supports:list sort -> sort -> bool) (e:expr) : bool =
  match e with
  | App _ (array :: _) ->
    (match Syntax.lambda_view array with
     | Some (bound, body) -> supports bound (get_sort body)
     | None -> false)
  | _ -> false

let beta_view_model (#base:sort -> Type0) (sigma:V.signature)
                    (supports:list sort -> sort -> bool)
                    (i:V.interpretation base sigma) (e:expr) : prop =
  match e with
  | App _ (array :: _) -> view_model sigma supports i array
  | _ -> True

let lemma_lambda_view (#base:sort -> Type0) (sigma:V.signature)
                      (supports:list sort -> sort -> bool)
                      (i:V.interpretation base sigma) (scope:list sort)
                      (rho:V.environment base sigma scope)
                      (e:expr) (bound:list sort) (body:expr)
  : Lemma (requires view_model sigma supports i e /\ supports bound (get_sort body) /\ D.scoped scope e /\
                    Syntax.lambda_view e == Some (bound, body))
          (ensures
            D.scoped (L.rev bound @ scope) body /\
            get_sort e == quant_sort Lambda_k bound (get_sort body) /\
            V.evaluate sigma i scope rho e ==
            V.evaluate sigma i scope rho
              (Quantifier Lambda_k bound (quant_sort Lambda_k bound (get_sort body)) body)) =
  match e with
  | Quantifier _ _ _ _ -> ()
  | App f [v] ->
    LP.rev_length bound;
    K.lemma_lift_under_scope (L.rev bound) scope v;
    assert (get_sort body == get_sort v);
    let left = V.evaluate_body sigma i scope rho bound body in
    let value = V.evaluate sigma i scope rho v in
    let pointwise (vs:V.arguments base sigma (L.rev bound))
      : Lemma (left vs == value) =
      K.lemma_lift_under sigma i (L.rev bound) scope vs rho v in
    FStar.Classical.forall_intro pointwise;
    let right = FE.on_dom_g (V.arguments base sigma (L.rev bound))
      (fun _ -> (value <: V.tree base)) in
    assert (FE.feq_g left right);
    FE.extensionality_g (V.arguments base sigma (L.rev bound)) (fun _ -> V.tree base) left right;
    assert (left == right);
    V.lemma_sort_eq (get_sort v) (get_sort v);
    assert (f == constant_decl bound (get_sort v));
    assert (V.evaluate_args sigma i scope rho [v] [get_sort v] == [value]);
    assert (i.application f [value] ==
            i.quantification Lambda_k bound (get_sort v)
              (constant_body sigma bound (get_sort v) value));
    lemma_constant_body sigma bound (get_sort v) value;
    assert (V.typed_body sigma bound (get_sort body) left ==
            constant_body sigma bound (get_sort v) value)
  | _ -> ()

let lemma_beta (#base:sort -> Type0) (sigma:V.signature)
               (supports:list sort -> sort -> bool)
               (i:V.interpretation base sigma) (scope:list sort)
               (rho:V.environment base sigma scope) (e result:expr)
  : Lemma (requires beta_view_model sigma supports i e /\ select_model sigma supports i /\
                    supported_beta supports e /\
                    D.scoped scope e /\ Syntax.beta e == Some result)
          (ensures D.scoped scope result /\ get_sort e == get_sort result /\
                   V.evaluate sigma i scope rho e == V.evaluate sigma i scope rho result) =
  match e with
  | App f (array :: args) ->
    (match Syntax.lambda_view array with
     | Some (bound, body) ->
       lemma_lambda_view sigma supports i scope rho array bound body;
       assert (f == select_decl bound (get_sort body));
       D.lemma_scoped_reverse_acc scope args [];
       lemma_reverse_sorts args [] bound [];
       lemma_evaluate_reverse_acc sigma i scope rho args [] bound [];
       let values = V.evaluate_args sigma i scope rho args bound in
       let actuals = L.rev args in
       let lambda_body = V.typed_body sigma bound (get_sort body)
         (V.evaluate_body sigma i scope rho bound body) in
       assert (V.evaluate_args sigma i scope rho actuals (L.rev bound) ==
               reverse_arguments sigma bound values);
       K.lemma_substitute sigma i scope rho actuals (L.rev bound) body result;
       assert (V.evaluate sigma i scope rho array ==
               i.quantification Lambda_k bound (get_sort body) lambda_body);
       assert (V.evaluate_args sigma i scope rho (array :: args) f.domain ==
               V.evaluate sigma i scope rho array :: values);
       assert (i.application f (V.evaluate sigma i scope rho array :: values) ==
               lambda_body (reverse_arguments sigma bound values))
     | None -> ())
  | _ -> ()
