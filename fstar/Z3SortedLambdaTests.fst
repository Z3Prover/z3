module Z3SortedLambdaTests

open Z3AstTheory
open FStar.List.Tot
module V = Z3DatatypeValue
module D = Z3ExprScope
module K = Z3SortedLambda
module Syntax = Z3LambdaSyntax

let integer = SortApp IntSymbol []
let inner = ArraySort [bool_sort] integer
let outer = ArraySort [integer] inner
let bound = [integer; bool_sort]
let constant = App (K.constant_decl bound outer) [Var 0 outer]
let body = Var 2 outer
let expanded = Quantifier Lambda_k bound (ArraySort bound outer) body

let nested_array_constant_view (#base:sort -> Type0) (sigma:V.signature)
                               (supports:list sort -> sort -> bool)
                               (i:V.interpretation base sigma)
                               (rho:V.environment base sigma [outer])
  : Lemma (requires K.constant_model sigma supports i /\ supports bound outer)
          (ensures D.scoped [outer] constant /\
                   D.scoped [bool_sort; integer; outer] body /\
                   V.evaluate sigma i [outer] rho constant ==
                   V.evaluate sigma i [outer] rho expanded) =
  assert_norm (D.scoped [outer] constant /\
               Syntax.lambda_view constant == Some (bound, body));
  K.lemma_lambda_view sigma supports i [outer] rho constant bound body

let nested_array_lambda_view (#base:sort -> Type0) (sigma:V.signature)
                             (supports:list sort -> sort -> bool)
                             (i:V.interpretation base sigma)
                             (rho:V.environment base sigma [outer])
  : Lemma (requires supports bound outer)
          (ensures V.evaluate sigma i [outer] rho expanded ==
                   V.evaluate sigma i [outer] rho
                     (Quantifier Lambda_k bound (quant_sort Lambda_k bound (get_sort body)) body)) =
  assert_norm (D.scoped [outer] expanded /\
               Syntax.lambda_view expanded == Some (bound, body));
  K.lemma_lambda_view sigma supports i [outer] rho expanded bound body

let combine = {
  decl_name = "lambda-combine"; domain = [integer; bool_sort; outer]; range = outer;
  interp = None; int_params = [];
}
let nested_lambda =
  Quantifier Lambda_k [inner] (ArraySort [inner] outer)
    (App combine [Var 2 integer; Var 1 bool_sort; Var 5 outer])
let beta_lambda =
  Quantifier Lambda_k bound (ArraySort bound (ArraySort [inner] outer)) nested_lambda
let beta_input =
  App (K.select_decl bound (ArraySort [inner] outer))
    [beta_lambda; Var 0 integer; Var 1 bool_sort]
let beta_result =
  Quantifier Lambda_k [inner] (ArraySort [inner] outer)
    (App combine [Var 1 integer; Var 2 bool_sort; Var 3 outer])

let heterogeneous_beta_under_lambda (#base:sort -> Type0) (sigma:V.signature)
                                    (supports:list sort -> sort -> bool)
                                    (i:V.interpretation base sigma)
                                    (rho:V.environment base sigma [integer; bool_sort; outer])
  : Lemma (requires K.select_model sigma supports i /\
                    supports bound (ArraySort [inner] outer))
          (ensures D.scoped [integer; bool_sort; outer] beta_input /\
                   D.scoped [integer; bool_sort; outer] beta_result /\
                   V.evaluate sigma i [integer; bool_sort; outer] rho beta_input ==
                   V.evaluate sigma i [integer; bool_sort; outer] rho beta_result) =
  assert_norm (D.scoped [integer; bool_sort; outer] beta_input /\
               Syntax.beta beta_input == Some beta_result);
  K.lemma_beta sigma supports i [integer; bool_sort; outer] rho beta_input beta_result

let constant_beta =
  App (K.select_decl bound outer) [constant; Var 1 integer; Var 2 bool_sort]

let nested_array_constant_beta (#base:sort -> Type0) (sigma:V.signature)
                               (supports:list sort -> sort -> bool)
                               (i:V.interpretation base sigma)
                               (rho:V.environment base sigma [outer; integer; bool_sort])
  : Lemma (requires K.constant_model sigma supports i /\ K.select_model sigma supports i /\
                    supports bound outer)
          (ensures D.scoped [outer; integer; bool_sort] constant_beta /\
                   V.evaluate sigma i [outer; integer; bool_sort] rho constant_beta ==
                   V.evaluate sigma i [outer; integer; bool_sort] rho (Var 0 outer)) =
  assert_norm (D.scoped [outer; integer; bool_sort] constant_beta /\
               Syntax.beta constant_beta == Some (Var 0 outer));
  K.lemma_beta sigma supports i [outer; integer; bool_sort] rho constant_beta (Var 0 outer)
