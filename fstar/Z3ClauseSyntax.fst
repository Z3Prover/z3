module Z3ClauseSyntax

open Z3AstTheory
open Z3OperatorTags
module C = Z3CanonicalOps
module CS = Z3ClausalSemantics

let eq_decl (s:sort) : func_decl =
  { decl_name = "="; domain = [s; s]; range = bool_sort; interp = Some op_eq; int_params = [] }

let mk_eq_expr (s t:expr) : expr = App (eq_decl (get_sort s)) [s; t]
let mk_iff_expr (a b:expr) : expr = App (eq_decl bool_sort) [a; b]

let true_expr : expr =
  App { decl_name = "true"; domain = []; range = bool_sort;
        interp = Some op_true; int_params = [] } []
let false_expr : expr =
  App { decl_name = "false"; domain = []; range = bool_sort;
        interp = Some op_false; int_params = [] } []

let not_decl : func_decl =
  { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
    interp = Some op_not; int_params = [] }
let mk_not_expr (a:expr) : expr = App not_decl [a]

let formula_clause (e:expr) : CS.clause =
  match e with
  | App f args ->
    if C.canonical_or f then args
    else if C.canonical_false f && args = [] then []
    else [e]
  | _ -> [e]

let consequence_covers (concl lit:expr) : bool =
  lit = concl ||
  (match concl with
   | App f args -> C.canonical_or f && FStar.List.Tot.mem lit args
   | _ -> false)

let rec clause_consequence (residual:CS.clause) (concl:expr)
  : Tot bool (decreases residual) =
  match residual with
  | [] -> true
  | l :: rest -> consequence_covers concl l && clause_consequence rest concl

let resolution_residual (c:expr) (units:list CS.literal) : CS.clause =
  match units with
  | [u] ->
    if CS.complementary c u then []
    else CS.unit_resolve (formula_clause c) units
  | _ -> CS.unit_resolve (formula_clause c) units
