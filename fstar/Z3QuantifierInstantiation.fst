module Z3QuantifierInstantiation

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module D = Z3Definitions
module S = Z3BinderSubstitution
module L = FStar.List.Tot

let substitute (args:list expr) (body:expr) : option expr = S.substitute args body

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

let lemma_substitute_sound (i:interpretation value) (rho:env value)
                          (args:list expr) (body inst:expr)
  : Lemma (requires quant_extensional i /\ substitute args body == Some inst)
          (ensures eval i body (shift (eval_args i args rho) rho) == eval i inst rho)
  = S.lemma_substitute i rho args body inst

let lemma_check_sound (i:interpretation value) (rho:env value)
                      (args:list expr) (formula:expr)
  : Lemma (requires quant_extensional i /\ boolean_model i /\ not_sound i /\ or_sound i /\
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
