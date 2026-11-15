module Z3CommutativitySyntax

open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax

let int_sort : sort = (SortApp IntSymbol [])

let arithmetic_decl (f:func_decl) : bool =
  f.domain = [int_sort; int_sort] && f.range = int_sort && f.int_params = [] &&
  ((f.decl_name = "+" && f.interp = Some op_plus) ||
   (f.decl_name = "*" && f.interp = Some op_mul))

let commutative_decl (f:func_decl) : bool =
  (match f.domain with
   | [s; t] -> s = t && f = eq_decl s
   | _ -> false) ||
  (f.domain = [bool_sort; bool_sort] && f.range = bool_sort && f.int_params = [] &&
   ((f.decl_name = "and" && f.interp = Some op_and) ||
    (f.decl_name = "or" && f.interp = Some op_or))) ||
  arithmetic_decl f

let commutativity_step (a b:expr) : bool =
  match a, b with
  | App f [x; y], App g [u; v] ->
    f = g && commutative_decl f && f.domain = [get_sort x; get_sort y] &&
    x = v && y = u
  | _, _ -> false
