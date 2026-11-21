module Z3SortedInstantiation

open Z3AstTheory
open FStar.List.Tot
module D = Z3ExprScope
module B = Z3SortedBinding
module Sub = Z3Substitution
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties

let instance_scopes (left right:list sort) (variables:list nat) (args:list expr) : prop =
  forall (n:nat{n < L.length left}).
    match Sub.argument n variables args with
    | Some e -> D.scoped right e /\ get_sort e == L.index left n
    | None -> True

let rec lemma_instantiate_scope (bound left right:list sort) (variables:list nat)
                                (args:list expr) (e result:expr)
  : Lemma (requires D.scoped (bound @ left) e /\
                    instance_scopes left right variables args /\
                    Sub.instantiate (L.length bound) variables args e == Some result)
          (ensures D.scoped (bound @ right) result /\ get_sort result == get_sort e)
          (decreases e) =
  LP.append_length bound left;
  LP.append_length bound right;
  match e, result with
  | Var n _, _ ->
    B.lemma_scope_index bound left n;
    if n < L.length bound then
      B.lemma_scope_index bound right n
    else (
      let a = Some?.v (Sub.argument (n - L.length bound) variables args) in
      B.lemma_lift_under_scope bound right a)
  | App f xs, App _ ys ->
    lemma_instantiate_args_scope bound left right variables args xs ys f.domain
  | Quantifier _ bs _ body, Quantifier _ _ _ body' ->
    LP.rev_length bs;
    LP.append_length (L.rev bs) bound;
    LP.append_assoc (L.rev bs) bound left;
    LP.append_assoc (L.rev bs) bound right;
    lemma_instantiate_scope (L.rev bs @ bound) left right variables args body body'
  | _, _ -> ()

and lemma_instantiate_args_scope (bound left right:list sort) (variables:list nat)
                                (args xs ys:list expr) (ss:list sort)
  : Lemma (requires D.scoped_args (bound @ left) xs /\ sorts_match xs ss /\
                    instance_scopes left right variables args /\
                    Sub.instantiate_args (L.length bound) variables args xs == Some ys)
          (ensures D.scoped_args (bound @ right) ys /\ sorts_match ys ss)
          (decreases xs) =
  match xs, ys, ss with
  | x :: rest, y :: tail, _ :: remaining ->
    lemma_instantiate_scope bound left right variables args x y;
    lemma_instantiate_args_scope bound left right variables args rest tail remaining
  | _, _, _ -> ()
