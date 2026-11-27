module Z3ConditionalRewriteSyntax

open Z3AstTheory
open Z3ClauseSyntax
module B = Z3BooleanRewriteSyntax
module A = Z3ArraySyntax
module R = Z3ArithmeticSyntax
module I = Z3IntegerRewriteSyntax
module L = FStar.List.Tot

(* The arguments other than the neutral literal of a conjunction or
   disjunction. *)
let rec drop_neutral (neutral:expr) (args:list expr) : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest ->
    if a = neutral then drop_neutral neutral rest else a :: drop_neutral neutral rest

(* A conjunction or disjunction with a true or false argument: its absorbing
   literal, or the remaining arguments. This is only a candidate; fold keeps
   it when the Boolean checker proves it equivalent. *)
let unit_fold (e:expr) : option expr =
  match e with
  | App f args ->
    let op = if f.decl_name = "and" then B.Conjunction else B.Disjunction in
    if not (B.connective_app op f args) then None
    else
      let neutral = if op = B.Conjunction then true_expr else false_expr in
      let absorbing = if op = B.Conjunction then false_expr else true_expr in
      if L.mem absorbing args then Some absorbing
      else
        let rest = drop_neutral neutral args in
        if L.length rest = L.length args then None
        else (match rest with
              | [] -> Some neutral
              | [a] -> Some a
              | _ -> Some (App (B.connective_decl op rest) rest))
  | _ -> None

(* Ground simplification after a guard is replaced: conditionals with a
   literal guard, equations and comparisons whose linear normal form is a
   constant (such as a comparison of numerals), and and/or with a literal
   argument. *)
let fold (e:expr) : expr =
  match A.ite_contract e with
  | Some t -> t
  | None ->
    if R.constant_equation e true_expr then true_expr
    else if R.constant_equation e false_expr then false_expr
    else if R.boolean_equivalent e true_expr then true_expr
    else if R.boolean_equivalent e false_expr then false_expr
    else match unit_fold e with
      | Some t -> if B.boolean_equiv 8 10 e t then t else e
      | None -> e

(* A guard is replaced only outside binders. Both sides of a proposed
   rewrite are checked in each branch, not against a fixed normal form. *)
let rec choose (guard:expr) (truth:bool) (e:expr) : Tot expr (decreases e) =
  if e = guard then (if truth then true_expr else false_expr)
  else match e with
  | App f args -> fold (App f (choose_args guard truth args))
  | _ -> e

and choose_args (guard:expr) (truth:bool) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> choose guard truth a :: choose_args guard truth rest

let rec condition (e:expr)
  : Tot (option (c:expr{get_sort c = bool_sort})) (decreases e) =
  match A.ite_parts e with
  | Some (c, _, _) -> Some c
  | None ->
    (match e with App _ args -> condition_args args | _ -> None)

and condition_args (args:list expr)
  : Tot (option (c:expr{get_sort c = bool_sort})) (decreases args) =
  match args with
  | [] -> None
  | a :: rest ->
    (match condition a with Some c -> Some c | None -> condition_args rest)

let base_equivalent (s t:expr) : bool =
  s = t || R.equivalent s t || B.boolean_equiv 8 10 s t || A.equivalent 8 s t ||
  I.equivalent s t

(* At least one branch must close without further splitting. This bounds
   work linearly in the fuel, even for independent conditionals. *)
let rec check (fuel:nat) (s t:expr) : Tot bool (decreases fuel) =
  if base_equivalent s t then true
  else if fuel = 0 then false
  else
    let _ = assert (fuel > 0) in
    let guard = match condition s with Some c -> Some c | None -> condition t in
    match guard with
    | None -> false
    | Some c ->
      if base_equivalent (choose c true s) (choose c true t) then
        check (fuel - 1) (choose c false s) (choose c false t)
      else if base_equivalent (choose c false s) (choose c false t) then
        check (fuel - 1) (choose c true s) (choose c true t)
      else false

let equivalent (s t:expr) : bool =
  get_sort s = get_sort t &&
  Some? (expression_budget 4096 s) && Some? (expression_budget 4096 t) &&
  check 64 s t

