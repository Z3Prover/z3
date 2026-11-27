module Z3SortedBindingTests

open Z3AstTheory
open FStar.List.Tot
module B = Z3ExprBinding
module D = Z3ExprScope
module L = FStar.List.Tot
module K = Z3SortedBinding
module Sub = Z3Substitution
module V = Z3DatatypeValue

let int_s = SortApp IntSymbol []
let inner_array_s = ArraySort [bool_sort] int_s
let outer_array_s = ArraySort [int_s] inner_array_s
let payload = Var 1 outer_array_s
let index = Var 0 int_s
let pair = {
  decl_name = "sorted-binding-pair";
  domain = [outer_array_s; int_s];
  range = outer_array_s;
  interp = None;
  int_params = [];
}
let open_term = App pair [payload; index]

let heterogeneous_scope_lifting ()
  : Lemma (
      D.scoped [int_s; outer_array_s] open_term /\
      D.scoped [bool_sort; int_s; int_s; outer_array_s]
        (B.lift 2 0 open_term) /\
      get_sort (B.lift 2 0 open_term) == get_sort open_term) =
  K.lemma_lift_under_scope [bool_sort; int_s] [int_s; outer_array_s] open_term

let lifting_through_nested_heterogeneous_binders ()
  : Lemma (
      let nested =
        Quantifier Lambda_k [bool_sort; inner_array_s]
          (quant_sort Lambda_k [bool_sort; inner_array_s] outer_array_s)
          (App pair [Var 3 outer_array_s; Var 2 int_s]) in
      D.scoped [int_s; outer_array_s] nested /\
      D.scoped [bool_sort; int_s; int_s; outer_array_s] (B.lift 2 0 nested) /\
      get_sort (B.lift 2 0 nested) == get_sort nested) =
  let nested =
    Quantifier Lambda_k [bool_sort; inner_array_s]
      (quant_sort Lambda_k [bool_sort; inner_array_s] outer_array_s)
      (App pair [Var 3 outer_array_s; Var 2 int_s]) in
  K.lemma_lift_under_scope [bool_sort; int_s] [int_s; outer_array_s] nested

let lifted_environment_relation (#base:sort -> Type0) (sigma:Z3DatatypeValue.signature)
                                (bound scope:list sort)
                                (vs:Z3DatatypeValue.arguments base sigma bound)
                                (rho:Z3DatatypeValue.environment base sigma scope)
  : Lemma (
      K.lift_environments sigma (L.length bound) 0 scope (bound @ scope)
        rho (Z3DatatypeValue.extend sigma scope bound vs rho)) =
  K.lemma_lift_under_environments sigma bound scope vs rho

let predicate = {
  decl_name = "sorted-binding-predicate";
  domain = [int_s; bool_sort; inner_array_s; outer_array_s; outer_array_s];
  range = bool_sort;
  interp = None;
  int_params = [];
}

let nested_substitution_body : expr =
  Quantifier Lambda_k [inner_array_s] (ArraySort [inner_array_s] bool_sort)
    (Quantifier Forall_k [bool_sort; int_s] bool_sort
      (App predicate [Var 0 int_s; Var 1 bool_sort; Var 2 inner_array_s;
                      Var 3 outer_array_s; Var 4 outer_array_s]))

let nested_substitution_result : expr =
  Quantifier Lambda_k [inner_array_s] (ArraySort [inner_array_s] bool_sort)
    (Quantifier Forall_k [bool_sort; int_s] bool_sort
      (App predicate [Var 0 int_s; Var 1 bool_sort; Var 2 inner_array_s;
                      Var 3 outer_array_s; Var 3 outer_array_s]))

let nested_open_substitution (#base:sort -> Type0) (sigma:V.signature)
                             (i:V.interpretation base sigma)
                             (rho:V.environment base sigma [outer_array_s])
  : Lemma (
      D.scoped [outer_array_s; outer_array_s] nested_substitution_body /\
      D.scoped [outer_array_s] nested_substitution_result /\
      V.evaluate sigma i [outer_array_s; outer_array_s]
        (V.extend sigma [outer_array_s] [outer_array_s]
          (V.evaluate_args sigma i [outer_array_s] rho [Var 0 outer_array_s] [outer_array_s])
          rho) nested_substitution_body ==
      V.evaluate sigma i [outer_array_s] rho nested_substitution_result) =
  assert_norm (D.scoped [outer_array_s; outer_array_s] nested_substitution_body /\
               D.scoped [outer_array_s] nested_substitution_result);
  assert_norm (Sub.substitute [Var 0 outer_array_s] nested_substitution_body ==
               Some nested_substitution_result);
  K.lemma_substitute sigma i [outer_array_s] rho [Var 0 outer_array_s] [outer_array_s]
    nested_substitution_body nested_substitution_result

let substitution_rejects_wrong_sort () : Lemma (
    Sub.substitute [Var 0 int_s] nested_substitution_body == None) =
  assert_norm (Sub.substitute [Var 0 int_s] nested_substitution_body == None)
