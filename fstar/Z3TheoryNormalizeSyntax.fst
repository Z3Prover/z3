module Z3TheoryNormalizeSyntax

open Z3AstTheory
open Z3ClauseSyntax

let rec contains (needle e:expr) : Tot bool (decreases e) =
  needle = e ||
  (match e with App _ args -> contains_args needle args | _ -> false)

and contains_args (needle:expr) (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> false
  | e :: rest -> contains needle e || contains_args needle rest

(* Equality premises hold in the current environment, not under binders. *)
let rec replace (source target e:expr) : Tot expr (decreases e) =
  if e = source then target
  else match e with
  | App f args -> App f (replace_args source target args)
  | _ -> e

and replace_args (source target:expr) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | e :: rest -> replace source target e :: replace_args source target rest

let constructor_term (e:expr) : bool =
  match e with App f args -> Some? (Z3DatatypeSyntax.constructor f args) | _ -> false

let constructor_replacement (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] ->
    if f <> eq_decl (get_sort a) || get_sort a <> get_sort b then None
    else if constructor_term b && not (constructor_term a) && not (contains a b)
    then Some (a, b)
    else if constructor_term a && not (constructor_term b) && not (contains b a)
    then Some (b, a)
    else None
  | _ -> None

let rec constructor_premise (facts:list expr) : Tot (option (expr & expr)) (decreases facts) =
  match facts with
  | [] -> None
  | e :: rest ->
    (match constructor_replacement e with Some pair -> Some pair | None -> constructor_premise rest)

