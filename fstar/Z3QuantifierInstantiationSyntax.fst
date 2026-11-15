module Z3QuantifierInstantiationSyntax

open Z3AstTheory
module S = Z3Substitution
module Scope = Z3ExprScope
module L = FStar.List.Tot
module C = Z3CanonicalOps

let substitute (args:list expr) (body:expr) : option expr = S.substitute args body

let check (args:list expr) (formula:expr) : bool =
  match formula with
  | App f [App n [Quantifier Forall_k bs s body]; inst] ->
    C.canonical_or f && C.canonical_not n && s = bool_sort &&
    get_sort body = bool_sort && get_sort inst = bool_sort &&
    sorts_match args bs && Scope.scoped_args [] args &&
    Scope.scoped [] (Quantifier Forall_k bs s body) &&
    substitute (L.rev args) body = Some inst
  | _ -> false
