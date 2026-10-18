module Z3QuantifierInstantiation

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open FStar.List.Tot
module D = Z3Definitions
module L = FStar.List.Tot

(* Arguments are closed and indexed in de Bruijn order, so inserting them
   under a binder does not require lifting their free variables. *)
let rec substitute_at (depth:nat) (args:list expr) (body:expr)
  : Tot (option expr) (decreases body) =
  match body with
  | Var n s ->
    if n < depth then Some body
    else if n - depth < L.length args && get_sort (L.index args (n - depth)) = s
    then Some (L.index args (n - depth)) else None
  | App f es ->
    (match substitute_args_at depth args es with
     | Some es' -> Some (App f es') | None -> None)
  | Quantifier k bs s b ->
    (match substitute_at (depth + L.length bs) args b with
     | Some b' -> Some (Quantifier k bs s b') | None -> None)

and substitute_args_at (depth:nat) (args es:list expr)
  : Tot (option (list expr)) (decreases es) =
  match es with
  | [] -> Some []
  | e :: rest ->
    (match substitute_at depth args e, substitute_args_at depth args rest with
     | Some e', Some rest' -> Some (e' :: rest') | _, _ -> None)

let substitute (args:list expr) (body:expr) : option expr =
  substitute_at 0 args body

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

let rec lemma_scoped_closed (scope:list sort) (e:expr)
  : Lemma (requires D.scoped scope e)
          (ensures closed_at (L.length scope) e)
          (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ es -> lemma_scoped_args_closed scope es
  | Quantifier _ bs _ body ->
    FStar.List.Tot.Properties.rev_length bs;
    FStar.List.Tot.Properties.append_length (L.rev bs) scope;
    lemma_scoped_closed (L.rev bs @ scope) body

and lemma_scoped_args_closed (scope:list sort) (args:list expr)
  : Lemma (requires D.scoped_args scope args)
          (ensures closed_at_args (L.length scope) args)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest -> lemma_scoped_closed scope a; lemma_scoped_args_closed scope rest

let rec lemma_scoped_reverse_acc (scope:list sort) (args acc:list expr)
  : Lemma (requires D.scoped_args scope args /\ D.scoped_args scope acc)
          (ensures D.scoped_args scope (L.rev_acc args acc))
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest -> lemma_scoped_reverse_acc scope rest (a :: acc)

let substitution_environment (i:interpretation value) (args:list expr) (depth:nat)
                             (source target:env value) : prop =
  forall (n:nat{n < depth + L.length args}).
    source n == (if n < depth then target n else eval i (L.index args (n - depth)) target)

let lemma_substitution_shift (i:interpretation value) (args:list expr) (depth:nat)
                             (source target:env value) (vs:list value)
  : Lemma (requires quant_extensional i /\ closed_at_args 0 args /\
                    substitution_environment i args depth source target)
          (ensures substitution_environment i args (depth + L.length vs)
                     (shift vs source) (shift vs target)) =
  let aux (n:nat{n < depth + L.length vs + L.length args})
    : Lemma (shift vs source n ==
        (if n < depth + L.length vs then shift vs target n
         else eval i (L.index args (n - (depth + L.length vs))) (shift vs target))) =
    if n >= depth + L.length vs then (
      let index = n - (depth + L.length vs) in
      lemma_closed_eval_args_env_irrelevant i args 0 target (shift vs target);
      lemma_eval_args_length i target args;
      lemma_eval_args_index i target args index;
      lemma_eval_args_index i (shift vs target) args index)
  in FStar.Classical.forall_intro aux

let rec lemma_substitute_at_sound (i:interpretation value) (depth:nat)
                                  (source target:env value)
                                  (args:list expr) (body inst:expr)
  : Lemma (requires quant_extensional i /\ closed_at_args 0 args /\
                    substitution_environment i args depth source target /\
                    substitute_at depth args body == Some inst)
          (ensures eval i body source == eval i inst target)
          (decreases body) =
  match body with
  | Var _ _ -> ()
  | App _ es ->
    lemma_substitute_args_at_sound i depth source target args es
      (Some?.v (substitute_args_at depth args es))
  | Quantifier _ bs _ b ->
    let b' = Some?.v (substitute_at (depth + L.length bs) args b) in
    let aux (vs:list value{L.length vs = L.length bs})
      : Lemma (eval i b (shift vs source) == eval i b' (shift vs target)) =
      lemma_substitution_shift i args depth source target vs;
      lemma_substitute_at_sound i (depth + L.length bs)
        (shift vs source) (shift vs target) args b b'
    in FStar.Classical.forall_intro aux

and lemma_substitute_args_at_sound (i:interpretation value) (depth:nat)
                                   (source target:env value)
                                   (args es instances:list expr)
  : Lemma (requires quant_extensional i /\ closed_at_args 0 args /\
                    substitution_environment i args depth source target /\
                    substitute_args_at depth args es == Some instances)
          (ensures eval_args i es source == eval_args i instances target)
          (decreases es) =
  match es, instances with
  | [], [] -> ()
  | e :: rest, inst :: remaining ->
    lemma_substitute_at_sound i depth source target args e inst;
    lemma_substitute_args_at_sound i depth source target args rest remaining
  | _, _ -> ()

let lemma_substitute_sound (i:interpretation value) (rho:env value)
                           (args:list expr) (body inst:expr)
  : Lemma (requires quant_extensional i /\ D.scoped_args [] args /\
                    substitute args body == Some inst)
          (ensures eval i body (shift (eval_args i args rho) rho) == eval i inst rho) =
  lemma_scoped_args_closed [] args;
  lemma_eval_args_length i rho args;
  let aux (n:nat{n < L.length args})
    : Lemma (shift (eval_args i args rho) rho n == eval i (L.index args n) rho) =
    lemma_eval_args_index i rho args n
  in
  FStar.Classical.forall_intro aux;
  lemma_substitute_at_sound i 0 (shift (eval_args i args rho) rho) rho args body inst

let lemma_check_sound (i:interpretation value) (rho:env value)
                      (args:list expr) (formula:expr)
  : Lemma (requires boolean_model i /\ not_sound i /\ or_sound i /\ quant_extensional i /\
                    forall_elimination_model i /\ check args formula)
          (ensures lit_true i rho formula)
  = match formula with
    | App f [App n [Quantifier Forall_k bs s body]; inst] ->
      lemma_sorts_length args bs;
      FStar.List.Tot.Properties.rev_length args;
      lemma_scoped_reverse_acc [] args [];
      lemma_eval_args_length i rho (L.rev args);
      lemma_substitute_sound i rho (L.rev args) body inst;
      FStar.Classical.excluded_middle
        (lit_true i rho (Quantifier Forall_k bs s body));
      assert (lit_true i rho (Quantifier Forall_k bs s body) ==>
              lit_true i (shift (eval_args i (L.rev args) rho) rho) body);
      (match eval i (Quantifier Forall_k bs s body) rho with VBool _ -> () | _ -> ())
    | _ -> ()
