module Z3IntegerDivisionSyntax

open Z3AstTheory
open Z3ClauseSyntax
module A = Z3LinearArithmeticAst
module R = Z3ArithmeticSyntax
module C = Z3CanonicalOps

let op_idiv : decl_kind = Z3OperatorTags.op_idiv
let op_mod : decl_kind = Z3OperatorTags.op_mod

let division (f:func_decl) (args:list expr) (remainder:bool) : bool =
  A.same_sort A.int_s args && FStar.List.Tot.length args = 2 &&
  A.application f args A.int_s (if remainder then "mod" else "div")
    (if remainder then op_mod else op_idiv)

let parts (e:expr) (remainder:bool) : option (expr & expr) =
  match e with
  | App f [a; b] -> if division f [a; b] remainder then Some (a, b) else None
  | _ -> None

let numeral (e:expr) (n:int) : bool = A.numeral e = Some (n, 1)

let nonzero_guard (guard b:expr) : bool =
  (guard = false_expr &&
   (match A.numeral b with Some (n, d) -> d = 1 && n <> 0 | None -> false)) ||
  (match A.comparison guard with
   | Some (A.Eq, x, z) -> x = b && numeral z 0
   | _ -> false)

let positive_guard (guard b:expr) : bool =
  (guard = false_expr &&
   (match A.numeral b with Some (n, d) -> d = 1 && n > 0 | None -> false)) ||
  (match A.comparison guard with
   | Some (A.Le, x, z) -> x = b && numeral z 0
   | _ -> false)

let decomposition (guard body:expr) : bool =
  match A.comparison body with
  | Some (A.Eq, a, App add [App mul [b; q]; r]) ->
    A.operation_of add [App mul [b; q]; r] = Some A.Add &&
    A.operation_of mul [b; q] = Some A.Mul &&
    parts q false = Some (a, b) && parts r true = Some (a, b) &&
    nonzero_guard guard b
  | _ -> false

let lower_bound (guard body:expr) : bool =
  match A.comparison body with
  | Some (A.Ge, r, z) ->
    numeral z 0 &&
    (match parts r true with Some (_, b) -> nonzero_guard guard b | None -> false)
  | _ -> false

let upper_bound (guard body:expr) : bool =
  match A.comparison body with
  | Some (A.Le, r, z) ->
    (match parts r true, A.numeral z with
     | Some (_, b), Some (n, d) ->
       d = 1 && A.numeral b = Some (n + 1, 1) && positive_guard guard b
     | _, _ ->
       match r with
       | App add [m; App mul [minus; b]] ->
         A.operation_of add [m; App mul [minus; b]] = Some A.Add &&
         A.operation_of mul [minus; b] = Some A.Mul &&
         numeral minus (-1) && numeral z (-1) &&
         (match parts m true with Some (_, divisor) -> divisor = b && positive_guard guard b
          | None -> false)
       | _ -> false)
  | _ -> false

let residual_bound (guard body:expr) : bool =
  match A.comparison body with
  | Some (A.Ge, App add [a; App mul [minus; App product [b; q]]], z) ->
    A.operation_of add [a; App mul [minus; App product [b; q]]] = Some A.Add &&
    A.operation_of mul [minus; App product [b; q]] = Some A.Mul &&
    A.operation_of product [b; q] = Some A.Mul &&
    numeral minus (-1) && numeral z 0 &&
    parts q false = Some (a, b) && nonzero_guard guard b
  | Some (A.Ge, App add [a; App mul [minus; b; q]], z) ->
    A.operation_of add [a; App mul [minus; b; q]] = Some A.Add &&
    A.operation_of mul [minus; b; q] = Some A.Mul &&
    numeral minus (-1) && numeral z 0 &&
    parts q false = Some (a, b) && nonzero_guard guard b
  | _ -> false

let check (e:expr) : bool =
  match e with
  | App f [guard; body] ->
    C.canonical_or f &&
    f.domain = [bool_sort; bool_sort] && f.range = bool_sort &&
    (decomposition guard body || lower_bound guard body ||
     upper_bound guard body || residual_bound guard body)
  | _ -> false

let scalar (e:expr) : option (int & expr) =
  match e with
  | App f [a; b] ->
    if A.operation_of f [a; b] <> Some A.Mul || f.range <> A.int_s then None
    else (match A.numeral a, A.numeral b with
    | Some (n, d), _ -> if d = 1 then Some (n, b) else None
    | _, Some (n, d) -> if d = 1 then Some (n, a) else None
    | _, _ -> None)
  | _ -> None

let scaled_division (e:expr) : option (int & expr & pos) =
  match parts e false with
  | Some (a, b) ->
    (match scalar a, A.numeral b with
     | Some (n, x), Some (d, den) ->
       if den = 1 && d > 0 then Some (n, x, d) else None
     | _, _ -> None)
  | None -> None

let cancellation (a b:expr) : bool =
  match scaled_division a, scaled_division b with
  | Some (n, x, d), Some (m, y, e) ->
    x = y && d % e = 0 && n = (d / e) * m
  | _, _ -> false

let folded_target (e:expr) : expr =
  match Z3ArraySyntax.ite_parts e with
  | Some (guard, _, other) -> if R.constant_equation guard false_expr then other else e
  | None -> e

let equivalent (a b:expr) : bool = cancellation a (folded_target b)

