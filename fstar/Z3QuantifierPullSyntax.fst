module Z3QuantifierPullSyntax

open Z3AstTheory
open Z3ClauseSyntax
open FStar.List.Tot
module D = Z3ExprBinding
module QN = Z3QuantifierNnfSyntax
module L = FStar.List.Tot
module C = Z3CanonicalOps

let rec boolean_args (args:list expr) : Tot bool (decreases args) =
  match args with
  | [] -> true
  | e :: rest -> get_sort e = bool_sort && boolean_args rest

let merge (kind:quantifier_kind) (sorts:list sort) (body:expr) : expr =
  match body with
  | Quantifier k bs s b ->
    if k = kind && s = bool_sort && get_sort b = bool_sort
    then Quantifier kind (sorts @ bs) bool_sort b
    else Quantifier kind sorts bool_sort body
  | _ -> Quantifier kind sorts bool_sort body

(* Pull the rightmost child first, preserving order within each binder block. *)
let rec split_quantifier (args:list expr)
  : Tot (option (list expr & quantifier_kind & list sort & expr & list expr)) (decreases args) =
  match args with
  | [] -> None
  | e :: rest ->
    (match split_quantifier rest with
     | Some (prefix, kind, sorts, body, suffix) ->
       Some (e :: prefix, kind, sorts, body, suffix)
     | None ->
       (match e with
        | Quantifier k bs s body ->
          if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort
          then Some ([], k, bs, body, rest) else None
        | _ -> None))

let rec normalize (fuel:nat) (e:expr) : Tot (option expr) (decreases fuel) =
  if fuel = 0 then None
  else match e with
  | Quantifier k bs s body ->
    if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort
    then (match normalize (fuel - 1) body with
          | Some b -> Some (merge k bs b)
          | None -> None)
    else Some e
  | App f args ->
    if (C.canonical_and f || C.canonical_or f) &&
       f.range = bool_sort && boolean_args args then
      (match split_quantifier args with
       | None -> Some e
       | Some (prefix, k, bs, body, suffix) ->
         let inside = App f (D.lift_args (L.length bs) 0 prefix @
                              (body :: D.lift_args (L.length bs) 0 suffix)) in
         (match normalize (fuel - 1) inside with
          | Some b -> Some (merge k bs b)
          | None -> None))
    else if f = not_decl then
      (match args with
       | [Quantifier k bs s body] ->
         if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort
         then Some (Quantifier (QN.dual k) bs bool_sort (mk_not_expr body))
         else Some e
       | _ -> Some e)
    else Some e
  | _ -> Some e

let check (a b:expr) : bool =
  match normalize 64 a, normalize 64 b with
  | Some x, Some y -> x = y
  | _, _ -> false
