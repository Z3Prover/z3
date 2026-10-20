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

(* Bounded certificate synthesis is not trusted: callers replay its weights
   through check against the original formulas. *)
type search_row = {
  search_poly: poly;
  search_weights: list int;
  search_strict: bool;
}

let rec search_basis (index size:nat) (weight:int) : Tot (list int) (decreases size) =
  if size = 0 then []
  else (if index = 0 then weight else 0) ::
       search_basis (if index = 0 then 0 else index - 1) (size - 1) (if index = 0 then 0 else weight)

let search_input (size index:nat) (weight:int) (positive:bool) (e:expr) : option search_row =
  match prepare_literal (weight, 1) positive e with
  | None -> None
  | Some p -> Some {
      search_poly = { p.poly with mono = P.collect p.poly.mono []; denom = 1 };
      search_weights = search_basis index size (weight * p.poly.denom);
      search_strict = p.strict;
    }

let rec search_inputs (size index:nat) (lits:list (bool & expr))
  : Tot (list search_row) (decreases lits) =
  match lits with
  | [] -> []
  | (positive, e) :: rest ->
    let tail = search_inputs size (index + 1) rest in
    let tail =
      match literal 16 positive e with
      | Some (true, Eq, _, _) ->
        (match search_input size index (-1) positive e with Some row -> row :: tail | None -> tail)
      | _ -> tail in
    (match search_input size index 1 positive e with Some row -> row :: tail | None -> tail)

let rec search_weights (a:int) (xs:list int) (b:int) (ys:list int)
  : Tot (option (list int)) (decreases xs) =
  match xs, ys with
  | [], [] -> Some []
  | x :: rest, y :: tail ->
    (match search_weights a rest b tail with
     | Some weights -> Some ((a * x + b * y) :: weights)
     | None -> None)
  | _, _ -> None

let rec search_coefficient (e:expr) (ms:list (int & expr)) : Tot int (decreases ms) =
  match ms with [] -> 0 | (n, v) :: rest -> if e = v then n else search_coefficient e rest

let search_combine (e:expr) (p q:search_row) : option search_row =
  let a = -search_coefficient e q.search_poly.mono in
  let b = search_coefficient e p.search_poly.mono in
  if a <= 0 || b <= 0 then None
  else match search_weights a p.search_weights b q.search_weights with
  | None -> None
  | Some weights ->
    let poly = P.add (P.scale a 1 p.search_poly) (P.scale b 1 q.search_poly) in
    Some { search_poly = { poly with mono = P.collect poly.mono [] };
           search_weights = weights; search_strict = p.search_strict || q.search_strict }

let rec search_pairs (budget:nat) (e:expr) (positive negative:list search_row)
  : Tot (option (list search_row)) (decreases %[budget; positive; negative]) =
  match positive, negative with
  | [], _ | _, [] -> Some []
  | p :: rest, _ ->
    let rec row (budget:nat) (qs:list search_row)
      : Tot (option (list search_row)) (decreases qs) =
      match qs with
      | [] -> Some []
      | q :: tail ->
        if budget = 0 then None
        else match search_combine e p q, row (budget - 1) tail with
        | Some combined, Some rows -> Some (combined :: rows)
        | _, _ -> None
    in
    match row budget negative with
    | None -> None
    | Some rows ->
      if length rows > budget then None else
      (match search_pairs (budget - length rows) e rest negative with
       | Some tail -> Some (rows @ tail)
       | None -> None)

let rec search_variable (rows:list search_row) : Tot (option expr) (decreases rows) =
  match rows with
  | [] -> None
  | row :: rest ->
    let rec first (ms:list (int & expr)) : Tot (option expr) (decreases ms) =
      match ms with [] -> None | (n, e) :: tail -> if n <> 0 then Some e else first tail in
    (match first row.search_poly.mono with Some e -> Some e | None -> search_variable rest)

let rec search_contradiction (rows:list search_row)
  : Tot (option (list coefficient)) (decreases rows) =
  match rows with
  | [] -> None
  | row :: rest ->
    if P.all_zero row.search_poly.mono &&
       (row.search_poly.cst > 0 || (row.search_poly.cst = 0 && row.search_strict))
    then Some (map (fun n -> let c:coefficient = n, 1 in c) row.search_weights)
    else search_contradiction rest

let rec search_partition (e:expr) (rows:list search_row)
  : Tot (list search_row & list search_row & list search_row) (decreases rows) =
  match rows with
  | [] -> [], [], []
  | row :: rest ->
    let positive, negative, zero = search_partition e rest in
    let n = search_coefficient e row.search_poly.mono in
    if n > 0 then row :: positive, negative, zero
    else if n < 0 then positive, row :: negative, zero
    else positive, negative, row :: zero

let rec search_eliminate (fuel:nat) (rows:list search_row)
  : Tot (option (list coefficient)) (decreases fuel) =
  match search_contradiction rows with
  | Some weights -> Some weights
  | None ->
    if fuel = 0 || length rows > 128 then None
    else match search_variable rows with
    | None -> None
    | Some e ->
      let positive, negative, zero = search_partition e rows in
      if length zero > 128 then None else
      (match search_pairs (128 - length zero) e positive negative with
       | Some pairs -> search_eliminate (fuel - 1) (zero @ pairs)
       | None -> None)

let synthesize (conclusion:expr) (facts:list expr) : option (list coefficient) =
  let lits = assumptions conclusion facts in
  if length lits > 32 then None
  else search_eliminate 16 (search_inputs (length lits) 0 lits)
