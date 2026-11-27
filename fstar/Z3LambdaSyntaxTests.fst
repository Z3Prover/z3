module Z3LambdaSyntaxTests

open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
module K = Z3LambdaSyntax

let integer = SortApp IntSymbol []
let array = ArraySort [integer] integer
let identity = Quantifier Lambda_k [integer] array (Var 0 integer)
let select = {
  decl_name = "select"; domain = [array; integer]; range = integer;
  interp = Some op_select; int_params = [];
}
let constant = {
  decl_name = "const"; domain = [integer]; range = array;
  interp = Some op_const_array; int_params = [];
}

let beta_and_constant_views () : Lemma (
    K.beta (App select [identity; Var 0 integer]) == Some (Var 0 integer) /\
    K.lambda_view (App constant [Var 0 integer]) == Some ([integer], Var 1 integer)) =
  assert_norm (
    K.beta (App select [identity; Var 0 integer]) == Some (Var 0 integer) /\
    K.lambda_view (App constant [Var 0 integer]) == Some ([integer], Var 1 integer))

let rejects_malformed_declarations () : Lemma (
    K.beta (App { select with int_params = [1] } [identity; Var 0 integer]) == None /\
    K.beta (App select [identity]) == None /\
    K.lambda_view (Quantifier Lambda_k [integer] integer (Var 0 integer)) == None /\
    K.lambda_view (App { constant with decl_name = "other" } [Var 0 integer]) == None) =
  assert_norm (
    K.beta (App { select with int_params = [1] } [identity; Var 0 integer]) == None /\
    K.beta (App select [identity]) == None /\
    K.lambda_view (Quantifier Lambda_k [integer] integer (Var 0 integer)) == None /\
    K.lambda_view (App { constant with decl_name = "other" } [Var 0 integer]) == None)

let extensional_uses_matching_lambda_binders () : Lemma (
    K.extensional (mk_eq_expr identity identity) ==
      Some (Quantifier Forall_k [integer] bool_sort
        (mk_eq_expr (Var 0 integer) (Var 0 integer))) /\
    K.extensional (mk_eq_expr identity (Var 0 array)) == None /\
    K.beta (Var 0 array) == None) =
  assert_norm (
    K.extensional (mk_eq_expr identity identity) ==
      Some (Quantifier Forall_k [integer] bool_sort
        (mk_eq_expr (Var 0 integer) (Var 0 integer))) /\
    K.extensional (mk_eq_expr identity (Var 0 array)) == None /\
    K.beta (Var 0 array) == None)
