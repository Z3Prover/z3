module Z3DefinitionRecognition

open Z3AstTheory
open Z3ClauseSyntax
open Z3BooleanRewriteSyntax
open Z3ArraySyntax
module A = Z3ArraySyntax
module Distinct = Z3DistinctAst
module L = FStar.List.Tot
open FStar.List.Tot

include Z3DefinitionSyntax

let binary (op:connective) (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] -> if connective_app op f [a; b] then Some (a, b) else None
  | _ -> None

let negation (e:expr) : option expr =
  match e with
  | App f [a] -> if native_bool_op f [a] = Z3BoundedBoolEquiv.BNot then Some a else None
  | _ -> None

let ite_clauses (a b:expr) : option (expr & expr & expr) =
  match binary Disjunction a, binary Disjunction b with
  | Some (nc, p), Some (c, q) ->
    if negation nc = Some c then Some (c, p, q) else None
  | _, _ -> None

let ite_definition (scope:list sort) (c x t y u:expr) : option definition =
  if x = y && get_sort t = get_sort u && get_sort c = bool_sort
  then make_definition scope x (App (A.term_ite_decl (get_sort t)) [c; t; u])
  else None

let clause_definition (scope:list sort) (a b:expr) : option definition =
  match ite_clauses a b with
  | Some (c, p, q) ->
    (match equality_parts p, equality_parts q with
     | Some (x, t), Some (y, u) ->
       (match ite_definition scope c x t y u with
        | Some d -> Some d
        | None ->
          (match ite_definition scope c x t u y with
           | Some d -> Some d
           | None ->
             (match ite_definition scope c t x y u with
              | Some d -> Some d | None -> ite_definition scope c t x u y)))
     | _, _ -> None)
  | None -> None

let boolean_definition (scope:list sort) (e:expr) : option definition =
  match binary Disjunction e with
  | Some (a, b) ->
    (match negation a with
     | Some n -> make_definition scope n b
     | None ->
       (match negation b with Some t -> make_definition scope a t | None -> None))
  | None -> None

let definition_of (e:expr) : option definition =
  let scope, b = strip_forall [] e in
  match equality_parts b with
  | Some (a, n) ->
    (match make_definition scope n a with
     | Some d -> Some d | None -> make_definition scope a n)
  | None ->
    (match binary Conjunction b with
     | Some (a, c) ->
       let sa, a' = strip_forall scope a in
       let sc, c' = strip_forall scope c in
       if sa <> sc then None
       else
         (match clause_definition sa a' c' with
          | Some d -> Some d
          | None ->
            (match clause_definition sa c' a' with
             | Some d -> Some d
             | None ->
               (match boolean_definition sa a' with
                | Some d -> Some d | None -> boolean_definition sa c')))
     | None -> boolean_definition scope b)

let add_definition (defs:list definition) (d:definition) : option (list definition) =
  match lookup defs d.symbol with
  | None -> Some (d :: defs)
  | Some old -> if old = d then Some defs else None

let rec acyclic (fuel:nat) (all defs:list definition) : Tot bool (decreases defs) =
  match defs with
  | [] -> true
  | d :: rest -> Some? (expand fuel all d.body) && acyclic fuel all rest

let rec acyclic_using (transform:expander) (fuel:nat) (all defs:list definition)
  : Tot (result:bool{result == acyclic fuel all defs}) (decreases defs) =
  match defs with
  | [] -> true
  | d :: rest ->
    Some? (transform fuel all d.body) && acyclic_using transform fuel all rest

let branch_equation (c a b:expr) (positive:bool) : bool =
  match A.ite_parts a with
  | Some (guard, t, u) -> c = guard && b = (if positive then t else u)
  | None -> false

let branch_axiom (e:expr) : bool =
  match binary Disjunction e with
  | Some (guard, equation) ->
    let c, positive =
      match negation guard with Some c -> c, true | None -> guard, false in
    (match equality_parts equation with
     | Some (a, b) -> branch_equation c a b positive || branch_equation c b a positive
     | None -> false)
  | None -> false

(* One extra level fully unfolds literal connectives omitted from the
   frontier, avoiding a boundary entry for every literal of a wide gate. *)
let propositional_tautology (e:expr) : bool =
  get_sort e = bool_sort &&
  Z3BooleanNormalForm.clause_tautology (boolean_cut (boolean_frontier 3 e) 4 e)

let rec boolean_budget (fuel:nat) (e:expr) : Tot (option nat) (decreases e) =
  if fuel = 0 then None
  else match e with
  | App f args ->
    if native_bool_op f args = Z3BoundedBoolEquiv.Opaque then Some (fuel - 1)
    else boolean_args_budget (fuel - 1) args
  | _ -> Some (fuel - 1)

and boolean_args_budget (fuel:nat) (args:list expr)
  : Tot (option nat) (decreases args) =
  match args with
  | [] -> Some fuel
  | a :: rest ->
    (match boolean_budget fuel a with
     | Some remaining -> boolean_args_budget remaining rest
     | None -> None)

let bounded_tautology (e:expr) : bool =
  Some? (boolean_budget 128 e) && boolean_equiv 8 10 e true_expr

let rec tautology (fuel:nat) (e:expr) : Tot bool (decreases %[fuel; 0]) =
  if fuel = 0 then false
  else match e with
  | Quantifier Forall_k bs s b -> s = bool_sort && tautology (fuel - 1) b
  | App f args ->
    if Distinct.distinct_axiom e || branch_axiom e || propositional_tautology e then true
    else if connective_app Conjunction f args then tautologies (fuel - 1) args
    else bounded_tautology e
  | _ -> bounded_tautology e

and tautologies (fuel:nat) (args:list expr)
  : Tot bool (decreases %[fuel; L.length args + 1]) =
  match args with
  | [] -> true
  | a :: rest -> tautology fuel a && tautologies fuel rest

let axiom_branch (e:expr) : bool =
  let _, b = strip_forall [] e in
  match binary Disjunction b with
  | Some (_, eq) -> Some? (equality_parts eq)
  | None -> false

let rec paired_definition (e:expr) (axioms:list expr)
  : Tot (option definition) (decreases axioms) =
  match axioms with
  | [] -> None
  | a :: rest ->
    let se, e' = strip_forall [] e in
    let sa, a' = strip_forall [] a in
    let candidate =
      if se <> sa then None
      else match clause_definition se e' a' with
           | Some d -> Some d
           | None -> clause_definition se a' e' in
    (match candidate with
     | Some d -> Some d
     | None -> paired_definition e rest)

let axiom_definition (e:expr) (branches:list expr) : option definition =
  let _, b = strip_forall [] e in
  let direct = Some? (equality_parts b) || Some? (binary Conjunction b) in
  if not (direct || axiom_branch e) || tautology 128 e then None
  else
    if direct then definition_of e
    else if axiom_branch e then paired_definition e branches
    else None

