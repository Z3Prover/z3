module Z3QuantifierInstantiation

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module D = Z3Definitions
module L = FStar.List.Tot

(* Arguments are indexed in de Bruijn order. Nested binders are deliberately
   excluded until capture-avoiding substitution has its own semantic proof. *)
let rec substitute (args:list expr) (body:expr) : Tot (option expr) (decreases body) =
  match body with
  | Var n s ->
    if n < L.length args && get_sort (L.index args n) = s
    then Some (L.index args n) else None
  | App f es ->
    (match substitute_args args es with
     | Some es' -> Some (App f es') | None -> None)
  | Quantifier _ _ _ _ -> None

and substitute_args (args es:list expr) : Tot (option (list expr)) (decreases es) =
  match es with
  | [] -> Some []
  | e :: rest ->
    (match substitute args e, substitute_args args rest with
     | Some e', Some rest' -> Some (e' :: rest') | _, _ -> None)

let check (args:list expr) (formula:expr) : bool =
  match formula with
  | App f [App n [Quantifier Forall_k bs s body]; inst] ->
    f.decl_name = "or" && n.decl_name = "not" && s = bool_sort &&
    get_sort body = bool_sort && get_sort inst = bool_sort &&
    sorts_match args bs && D.scoped_args [] args &&
    D.scoped [] (Quantifier Forall_k bs s body) &&
    substitute (L.rev args) body = Some inst
  | _ -> false

let forall_elimination_model (i:interpretation value) : prop =
  forall (bs:list sort) (body:expr) (rho:env value)
         (vs:list value{L.length vs = L.length bs}).
    lit_true i rho (Quantifier Forall_k bs bool_sort body) ==>
    lit_true i (shift vs rho) body

let rec lemma_sorts_length (args:list expr) (sorts:list sort)
  : Lemma (requires sorts_match args sorts)
          (ensures L.length args == L.length sorts)
          (decreases args) =
  match args, sorts with
  | _ :: rest, _ :: remaining -> lemma_sorts_length rest remaining
  | _, _ -> ()

let rec lemma_eval_args_length (i:interpretation value) (rho:env value) (args:list expr)
  : Lemma (L.length (eval_args i args rho) == L.length args) (decreases args) =
  match args with
  | [] -> ()
  | _ :: rest -> lemma_eval_args_length i rho rest

let rec lemma_eval_args_index (i:interpretation value) (rho:env value)
                              (args:list expr) (n:nat)
  : Lemma (requires n < L.length args /\ n < L.length (eval_args i args rho))
          (ensures L.index (eval_args i args rho) n == eval i (L.index args n) rho)
          (decreases args) =
  match args with
  | [] -> ()
  | _ :: rest -> if n = 0 then () else lemma_eval_args_index i rho rest (n - 1)

let rec lemma_substitute_sound (i:interpretation value) (rho:env value)
                               (args:list expr) (body inst:expr)
  : Lemma (requires substitute args body == Some inst)
          (ensures eval i body (shift (eval_args i args rho) rho) == eval i inst rho)
          (decreases body) =
  match body with
  | Var n _ ->
    lemma_eval_args_length i rho args;
    lemma_eval_args_index i rho args n
  | App _ es -> lemma_substitute_args_sound i rho args es (Some?.v (substitute_args args es))
  | Quantifier _ _ _ _ -> ()

and lemma_substitute_args_sound (i:interpretation value) (rho:env value)
                                (args es instances:list expr)
  : Lemma (requires substitute_args args es == Some instances)
          (ensures eval_args i es (shift (eval_args i args rho) rho) == eval_args i instances rho)
          (decreases es) =
  match es, instances with
  | [], [] -> ()
  | e :: rest, inst :: remaining ->
    lemma_substitute_sound i rho args e inst;
    lemma_substitute_args_sound i rho args rest remaining
  | _, _ -> ()

let lemma_check_sound (i:interpretation value) (rho:env value)
                      (args:list expr) (formula:expr)
  : Lemma (requires boolean_model i /\ not_sound i /\ or_sound i /\
                    forall_elimination_model i /\ check args formula)
          (ensures lit_true i rho formula)
  = match formula with
    | App f [App n [Quantifier Forall_k bs s body]; inst] ->
      lemma_sorts_length args bs;
      FStar.List.Tot.Properties.rev_length args;
      lemma_eval_args_length i rho (L.rev args);
      lemma_substitute_sound i rho (L.rev args) body inst;
      FStar.Classical.excluded_middle
        (lit_true i rho (Quantifier Forall_k bs s body));
      assert (lit_true i rho (Quantifier Forall_k bs s body) ==>
              lit_true i (shift (eval_args i (L.rev args) rho) rho) body);
      (match eval i (Quantifier Forall_k bs s body) rho with VBool _ -> () | _ -> ())
    | _ -> ()
