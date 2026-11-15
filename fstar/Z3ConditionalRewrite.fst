module Z3ConditionalRewrite

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
module B = Z3BooleanRewrite
module A = Z3ArrayRewrite
module R = Z3ArithmeticRewrite
module I = Z3IntegerRewrite
module E = Z3LinearArithmeticEmbed
module L = FStar.List.Tot

include Z3ConditionalRewriteSyntax

let rewrite_model (i:interpretation value) : prop =
  A.rewrite_model i /\ (exists (nu:value -> FStar.Real.real). E.numeric_model i nu)

let lemma_fold_sound (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires rewrite_model i)
          (ensures eval i (fold e) rho == eval i e rho) =
  match A.ite_contract e with
  | Some t -> A.lemma_ite_contract i rho e t
  | None ->
    if R.constant_equation e true_expr then
      R.lemma_equivalent_with_numeric_model e true_expr i rho
    else if R.constant_equation e false_expr then
      R.lemma_equivalent_with_numeric_model e false_expr i rho
    else if R.boolean_equivalent e true_expr then
      R.lemma_equivalent_with_numeric_model e true_expr i rho
    else if R.boolean_equivalent e false_expr then
      R.lemma_equivalent_with_numeric_model e false_expr i rho
    else match unit_fold e with
      | Some t -> if B.boolean_equiv 8 10 e t then B.lemma_boolean_equiv_sound 8 10 i rho e t
      | None -> ()

let rec lemma_choose_sound (i:interpretation value) (rho:env value)
                           (guard:expr) (truth:bool) (e:expr)
  : Lemma (requires rewrite_model i /\ eval i guard rho == VBool truth)
          (ensures eval i (choose guard truth e) rho == eval i e rho)
          (decreases e) =
  if e = guard then ()
  else match e with
  | App f args ->
    lemma_choose_args_sound i rho guard truth args;
    lemma_fold_sound i rho (App f (choose_args guard truth args))
  | _ -> ()

and lemma_choose_args_sound (i:interpretation value) (rho:env value)
                            (guard:expr) (truth:bool) (args:list expr)
  : Lemma (requires rewrite_model i /\ eval i guard rho == VBool truth)
          (ensures eval_args i (choose_args guard truth args) rho == eval_args i args rho)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_choose_sound i rho guard truth a;
    lemma_choose_args_sound i rho guard truth rest

let lemma_base_equivalent_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires rewrite_model i /\ base_equivalent s t)
          (ensures eval i s rho == eval i t rho) =
  if s = t then ()
  else if R.equivalent s t then R.lemma_equivalent_with_numeric_model s t i rho
  else if B.boolean_equiv 8 10 s t then B.lemma_boolean_equiv_sound 8 10 i rho s t
  else if A.equivalent 8 s t then A.lemma_equivalent_sound 8 i rho s t
  else I.lemma_equivalent_sound i rho s t

let rec lemma_check_sound (fuel:nat) (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires rewrite_model i /\ check fuel s t)
          (ensures eval i s rho == eval i t rho)
          (decreases fuel) =
  if base_equivalent s t then lemma_base_equivalent_sound i rho s t
  else if fuel > 0 then (
    let guard = match condition s with Some c -> Some c | None -> condition t in
    match guard with
    | None -> ()
    | Some c ->
      match eval i c rho with
      | VBool truth ->
        lemma_choose_sound i rho c truth s;
        lemma_choose_sound i rho c truth t;
        if base_equivalent (choose c true s) (choose c true t) then (
          if truth then lemma_base_equivalent_sound i rho (choose c true s) (choose c true t)
          else lemma_check_sound (fuel - 1) i rho (choose c false s) (choose c false t))
        else (
          if truth then lemma_check_sound (fuel - 1) i rho (choose c true s) (choose c true t)
          else lemma_base_equivalent_sound i rho (choose c false s) (choose c false t))
      | _ -> ())

let lemma_equivalent_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires rewrite_model i /\ equivalent s t)
          (ensures eval i s rho == eval i t rho) =
  lemma_check_sound 64 i rho s t
