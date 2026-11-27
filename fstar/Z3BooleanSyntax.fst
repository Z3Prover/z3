module Z3BooleanSyntax

open Z3AstTheory
open Z3OperatorTags
open FStar.List.Tot
module B = Z3BoundedBoolEquiv
module R = Z3ClauseSyntax

let rec boolean_args (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | a :: rest -> get_sort a = bool_sort && boolean_args rest

let boolean_ite_decl : func_decl =
  { decl_name = "if"; domain = [bool_sort; bool_sort; bool_sort];
    range = bool_sort; interp = Some op_ite; int_params = [] }

let boolean_xor_decl : func_decl =
  { decl_name = "xor"; domain = [bool_sort; bool_sort];
    range = bool_sort; interp = Some op_xor; int_params = [] }

let native_bool_op (f:func_decl) (args:list expr) : B.bool_op =
  if not (boolean_args args) then B.Opaque
  else if f = R.and_decl args && boolean_args args then B.BNary B.And
  else if f = R.or_decl args && boolean_args args then B.BNary B.Or
  else if f = { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
                interp = Some op_not; int_params = [] } && length args = 1
  then B.BNot
  else if (f.decl_name = "=>" || f.decl_name = "implies") &&
          f.domain = [bool_sort; bool_sort] && f.range = bool_sort &&
          f.interp = Some op_implies && f.int_params = [] && length args = 2
  then B.BImplies
  else if f = boolean_ite_decl && length args = 3 then B.BIte
  else if f = boolean_xor_decl && length args = 2 then B.BNary B.Xor
  else if f = R.eq_decl bool_sort && length args = 2 then B.BEq
  else if f = { decl_name = "true"; domain = []; range = bool_sort;
                interp = Some op_true; int_params = [] } && args = []
  then B.BTrue
  else if f = { decl_name = "false"; domain = []; range = bool_sort;
                interp = Some op_false; int_params = [] } && args = []
  then B.BFalse
  else B.Opaque

let rec boolean_nodes (depth:nat) (e:expr) : Tot (list expr) (decreases e) =
  match e with
  | App f args ->
    (match native_bool_op f args with
     | B.BTrue | B.BFalse -> []
     | B.Opaque -> [e]
     | _ -> e :: (if depth = 0 then [] else boolean_nodes_args (depth - 1) args))
  | _ -> [e]

and boolean_nodes_args (depth:nat) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> boolean_nodes depth a @ boolean_nodes_args depth rest
