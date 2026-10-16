module Z3LinearArithmeticAst

#set-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open FStar.List.Tot
module P = Z3LinearArithmeticTheory

type poly = P.polynomial expr
type contribution = P.contribution expr
type coefficient = int & pos
type relation = | Le | Lt | Ge | Gt | Eq
type operation = | Add | Mul | Sub | Div | ToReal

let int_s : sort = BaseSort "Int"
let real_s : sort = BaseSort "Real"
let numeric_sort (s:sort) : bool = s = int_s || s = real_s

let rec same_sort (s:sort) (args:list expr) : Tot bool (decreases args) =
  match args with [] -> true | a :: rest -> get_sort a = s && same_sort s rest

let application (f:func_decl) (args:list expr) (s:sort) (name:string) (tag:decl_kind) : bool =
  f = { decl_name = name; domain = map get_sort args; range = s;
        interp = Some tag; int_params = [] }

let numeral (e:expr) : option coefficient =
  match e with
  | App f [] ->
    if numeric_sort f.range && f.domain = [] && f.interp = Some op_num_rational then
      (match f.int_params with
       | [n; d] -> if d > 0 && (f.range = real_s || d = 1) then Some (n, d) else None
       | _ -> None)
    else None
  | _ -> None

let operation_of (f:func_decl) (args:list expr) : option operation =
  let s = f.range in
  if application f args real_s "to_real" op_to_real then
    (match args with [a] -> if get_sort a = int_s then Some ToReal else None | _ -> None)
  else if not (numeric_sort s && same_sort s args) then None
  else if application f args s "+" op_arith_add ||
          (s = int_s && length args = 2 && application f args s "+" op_plus)
  then Some Add
  else if application f args s "*" op_arith_mul ||
          (s = int_s && length args = 2 && application f args s "*" op_mul)
  then Some Mul
  else if application f args s "-" op_arith_sub && Cons? args then Some Sub
  else if s = real_s && length args = 2 && application f args s "/" op_arith_div then Some Div
  else None

let subtract (ps:list poly) : option poly =
  match ps with
  | [] -> None
  | [p] -> Some (P.scale (-1) 1 p)
  | p :: rest -> Some (P.add p (P.scale (-1) 1 (P.sum rest)))

let divide (p q:poly) : option poly =
  if not (P.all_zero q.mono) || q.cst = 0 then None
  else if q.cst > 0 then Some (P.scale q.denom q.cst p)
  else Some (P.scale (-q.denom) (-q.cst) p)

let combine (op:operation) (ps:list poly) (e:expr) : option poly =
  match op, ps with
  | Add, _ -> Some (P.sum ps)
  | Mul, _ -> (match P.product ps with Some p -> Some p | None -> Some (P.variable e))
  | Sub, _ -> subtract ps
  | Div, [p; q] -> divide p q
  | ToReal, [p] -> Some p
  | _, _ -> None

let rec linearize (fuel:nat) (e:expr) : Tot (option poly) (decreases %[fuel; 0]) =
  if fuel = 0 || not (numeric_sort (get_sort e)) then None
  else match numeral e with
  | Some (n, d) -> Some (P.constant n d)
  | None ->
    (match e with
     | App f args ->
       (match operation_of f args with
        | None -> Some (P.variable e)
        | Some op ->
          (match linearize_args (fuel - 1) args with
           | None -> None
           | Some ps -> combine op ps e))
     | _ -> Some (P.variable e))

and linearize_args (fuel:nat) (args:list expr)
  : Tot (option (list poly)) (decreases %[fuel; 1; args]) =
  match args with
  | [] -> Some []
  | a :: rest ->
    (match linearize fuel a, linearize_args fuel rest with
     | Some p, Some ps -> Some (p :: ps)
     | _, _ -> None)

let lemma_linearize_application (fuel:pos) (f:func_decl) (args:list expr) (op:operation)
  : Lemma (requires numeric_sort f.range /\ numeral (App f args) == None /\
                    operation_of f args == Some op)
          (ensures linearize fuel (App f args) ==
                   (match linearize_args (fuel - 1) args with
                    | None -> None
                    | Some ps -> combine op ps (App f args))) =
  match linearize_args (fuel - 1) args with
  | None -> ()
  | Some _ -> ()

let comparison (e:expr) : option (relation & expr & expr) =
  match e with
  | App f [a; b] ->
    let s = get_sort a in
    if not (numeric_sort s && get_sort b = s) then None
    else if f = eq_decl s then Some (Eq, a, b)
    else if application f [a; b] bool_sort "<=" op_arith_le then Some (Le, a, b)
    else if application f [a; b] bool_sort "<" op_arith_lt then Some (Lt, a, b)
    else if application f [a; b] bool_sort ">=" op_arith_ge then Some (Ge, a, b)
    else if application f [a; b] bool_sort ">" op_arith_gt then Some (Gt, a, b)
    else None
  | _ -> None

let rec literal (fuel:nat) (positive:bool) (e:expr)
  : Tot (option (bool & relation & expr & expr)) (decreases fuel) =
  if fuel = 0 then None
  else match e with
  | App f [a] ->
    if f = { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
             interp = Some op_not; int_params = [] } then literal (fuel - 1) (not positive) a
    else None
  | _ ->
    (match comparison e with
     | Some (r, a, b) -> Some (positive, r, a, b)
     | None -> None)

let oriented (positive:bool) (r:relation) (p q:poly) : poly & bool =
  let reversed = (positive && (r = Ge || r = Gt)) ||
                 (not positive && (r = Le || r = Lt)) in
  let strict = if positive then r = Lt || r = Gt else r = Le || r = Ge in
  ((if reversed then P.add q (P.scale (-1) 1 p) else P.add p (P.scale (-1) 1 q)), strict)

let weighted (c:coefficient) (positive:bool) (r:relation) (integer:bool) (p q:poly)
  : contribution =
  let n, d = c in
  let raw, strict = oriented positive r p q in
  let integral = integer && r <> Eq && strict in
  let raw = if integral then { raw with cst = raw.cst + raw.denom } else raw in
  let weight = if r = Eq || n > 0 then n else -n in
  { P.poly = P.scale weight d raw; strict = strict && not integral }

let prepare_literal (c:coefficient) (positive:bool) (e:expr) : option contribution =
  let n, d = c in
  if n = 0 then Some { P.poly = P.zero; strict = false }
  else match literal 16 positive e with
  | None -> None
  | Some (p, r, a, b) ->
    if r = Eq && not p then None
    else match linearize 256 a, linearize 256 b with
    | Some pa, Some pb -> Some (weighted c p r (get_sort a = int_s) pa pb)
    | _, _ -> None

let rec prepare (lits:list (bool & expr)) (cs:list coefficient)
  : Tot (option (list contribution)) (decreases lits) =
  match lits, cs with
  | [], [] -> Some []
  | (p, e) :: rest, c :: tail ->
    (match prepare_literal c p e, prepare rest tail with
     | Some a, Some ps -> Some (a :: ps)
     | _, _ -> None)
  | _, _ -> None

let positive_literal (e:expr) : bool & expr = (true, e)
let negative_literal (e:expr) : bool & expr = (false, e)

let assumptions (conclusion:expr) (facts:list expr) : list (bool & expr) =
  map positive_literal facts @ map negative_literal (formula_clause conclusion)

let check (cs:list coefficient) (conclusion:expr) (facts:list expr) : bool =
  match prepare (assumptions conclusion facts) cs with
  | Some ps -> P.accepts ps
  | None -> false
