module Z3LambdaSyntax

open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
module Binding = Z3ExprBinding
module Sub = Z3Substitution
module L = FStar.List.Tot

let const_array (f:func_decl) (v:expr) : bool =
  match f.range with
  | ArraySort bs element ->
    bs <> [] && element = get_sort v &&
    f = { decl_name = "const"; domain = [element]; range = ArraySort bs element;
          interp = Some op_const_array; int_params = [] }
  | _ -> false

let select_decl (f:func_decl) (array:expr) (args:list expr) : bool =
  match get_sort array with
  | ArraySort bs element ->
    sorts_match args bs &&
    f = { decl_name = "select"; domain = get_sort array :: bs; range = element;
          interp = Some op_select; int_params = [] }
  | _ -> false

let lambda_view (e:expr) : option (list sort & expr) =
  match e with
  | Quantifier Lambda_k bs s body ->
    if s = quant_sort Lambda_k bs (get_sort body) then Some (bs, body) else None
  | App f [v] ->
    if const_array f v then
      (match f.range with
       | ArraySort bs _ -> Some (bs, Binding.lift (L.length bs) 0 v)
       | _ -> None)
    else None
  | _ -> None

let extensional (e:expr) : option expr =
  match e with
  | App f [a; b] ->
    if f = eq_decl (get_sort a) && get_sort a = get_sort b then
      (match lambda_view a, lambda_view b with
       | Some (bs, left), Some (bs', right) ->
         if bs = bs' && get_sort left = get_sort right
         then Some (Quantifier Forall_k bs bool_sort (mk_eq_expr left right)) else None
       | _, _ -> None)
    else None
  | _ -> None

let beta (e:expr) : option expr =
  match e with
  | App f (array :: args) ->
    if select_decl f array args then
      (match lambda_view array with
       | Some (bs, body) -> Sub.substitute (L.rev args) body
       | _ -> None)
    else None
  | _ -> None
