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

let rewrite_model (i:interpretation value) : prop =
  A.rewrite_model i /\ (exists (nu:value -> FStar.Real.real). E.numeric_model i nu)

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

let lemma_base_equivalent_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires rewrite_model i /\ base_equivalent s t)
          (ensures eval i s rho == eval i t rho) =
  if s = t then ()
  else if R.equivalent s t then R.lemma_equivalent_with_numeric_model s t i rho
  else if B.boolean_equiv 8 10 s t then B.lemma_boolean_equiv_sound 8 10 i rho s t
  else if A.equivalent 8 s t then A.lemma_equivalent_sound 8 i rho s t
  else I.lemma_equivalent_sound i rho s t

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

let equivalent (s t:expr) : bool =
  get_sort s = get_sort t &&
  Some? (expression_budget 4096 s) && Some? (expression_budget 4096 t) &&
  check 64 s t

let lemma_equivalent_sound (i:interpretation value) (rho:env value) (s t:expr)
  : Lemma (requires rewrite_model i /\ equivalent s t)
          (ensures eval i s rho == eval i t rho) =
  lemma_check_sound 64 i rho s t
