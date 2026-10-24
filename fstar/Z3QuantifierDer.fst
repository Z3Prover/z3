module Z3QuantifierDer

open Z3AstTheory
open Z3ValueTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open FStar.List.Tot
module B = Z3BooleanRewrite
module D = Z3Definitions
module Q = Z3QuantifierNnf
module V = Z3QuantifierVacuity
module P = Z3QuantifierPull
module R = Z3QuantifierReduce
module L = FStar.List.Tot

let rec substitute (n:nat) (term body:expr) : Tot expr (decreases body) =
  match body with
  | Var j s -> if j = n then term else Var (if j < n then j else j - 1) s
  | App f args -> App f (substitute_args n term args)
  | Quantifier k bs s b ->
    Quantifier k bs s (substitute (n + L.length bs) (D.lift (L.length bs) 0 term) b)

and substitute_args (n:nat) (term:expr) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest -> substitute n term a :: substitute_args n term rest

let rec lemma_substitute_sound (n:nat) (term body:expr)
                               (i:interpretation value) (source target:env value)
  : Lemma (requires quant_extensional i /\ V.removed_environment n source target /\
                    source n == eval i term target)
          (ensures eval i body source == eval i (substitute n term body) target)
          (decreases body) =
  match body with
  | Var _ _ -> ()
  | App _ args -> lemma_substitute_args_sound n term args i source target
  | Quantifier _ bs _ b ->
    let aux (vs:list value{L.length vs = L.length bs})
      : Lemma (eval i b (shift vs source) ==
               eval i (substitute (n + L.length bs) (D.lift (L.length bs) 0 term) b)
                 (shift vs target)) =
      V.lemma_removed_shift n source target vs;
      P.lemma_lift_under i term target vs;
      lemma_substitute_sound (n + L.length bs) (D.lift (L.length bs) 0 term)
        b i (shift vs source) (shift vs target)
    in FStar.Classical.forall_intro aux

and lemma_substitute_args_sound (n:nat) (term:expr) (args:list expr)
                                (i:interpretation value) (source target:env value)
  : Lemma (requires quant_extensional i /\ V.removed_environment n source target /\
                    source n == eval i term target)
          (ensures eval_args i args source == eval_args i (substitute_args n term args) target)
          (decreases args) =
  match args with
  | [] -> ()
  | a :: rest ->
    lemma_substitute_sound n term a i source target;
    lemma_substitute_args_sound n term rest i source target

let gate (universal:bool) (guard body:expr) : expr =
  App { decl_name = (if universal then "or" else "and");
        domain = [bool_sort; bool_sort]; range = bool_sort;
        interp = Some (if universal then op_or else op_and); int_params = [] }
    [ (if universal then mk_not_expr guard else guard); body ]

let guarded (universal:bool) (n:nat) (term body:expr) : bool =
  let variable = Var n (get_sort term) in
  B.boolean_equiv 8 10 body (gate universal (mk_eq_expr variable term) body) ||
  B.boolean_equiv 8 10 body (gate universal (mk_eq_expr term variable) body)

let lemma_guarded_outside (universal:bool) (n:nat) (term body:expr)
                          (i:interpretation value) (rho:env value)
  : Lemma (requires B.boolean_rewrite_model i /\ eq_sound i /\ guarded universal n term body /\
                    ~(rho n == eval i term rho))
          (ensures lit_true i rho body <==> universal) =
  let variable = Var n (get_sort term) in
  let guard =
    if B.boolean_equiv 8 10 body (gate universal (mk_eq_expr variable term) body)
    then mk_eq_expr variable term else mk_eq_expr term variable in
  B.lemma_boolean_equiv_sound 8 10 i rho body (gate universal guard body);
  assert (~(lit_true i rho guard));
  if universal then (
    match eval i guard rho with VBool _ -> () | _ -> ())

let rec lemma_insert_index (n:nat) (v:value) (vs:list value)
  : Lemma (requires n <= L.length vs)
          (ensures n < L.length (V.insert n v vs) /\ L.index (V.insert n v vs) n == v)
          (decreases vs) =
  V.lemma_insert_erase n v vs;
  if n > 0 then match vs with [] -> () | _ :: rest -> lemma_insert_index (n - 1) v rest

let lemma_assignments (universal:bool) (n count:nat) (term lowered body:expr)
                      (i:interpretation value) (rho:env value)
  : Lemma (requires B.boolean_rewrite_model i /\ eq_sound i /\ quant_extensional i /\
                    n < count /\ V.lower n term == Some lowered /\ guarded universal n term body)
          (ensures V.all_assignments i rho count body universal <==>
                   V.all_assignments i rho (count - 1) (substitute n lowered body) universal) =
  FStar.Classical.impl_intro
    #(V.all_assignments i rho count body universal)
    #(V.all_assignments i rho (count - 1) (substitute n lowered body) universal)
    (fun _ ->
      let aux (vs:list value{L.length vs = count - 1})
        : Lemma (lit_true i (shift vs rho) (substitute n lowered body) <==> universal) =
        let chosen = eval i lowered (shift vs rho) in
        let full = V.insert n chosen vs in
        V.lemma_insert_erase n chosen vs;
        lemma_insert_index n chosen vs;
        V.lemma_erased_environment n full rho;
        lemma_substitute_sound n lowered body i (shift full rho) (shift vs rho)
      in FStar.Classical.forall_intro aux);
  FStar.Classical.impl_intro
    #(V.all_assignments i rho (count - 1) (substitute n lowered body) universal)
    #(V.all_assignments i rho count body universal)
    (fun _ ->
      let aux (vs:list value{L.length vs = count})
        : Lemma (lit_true i (shift vs rho) body <==> universal) =
        V.lemma_erase_length n vs;
        V.lemma_erased_environment n vs rho;
        let target = shift (V.erase n vs) rho in
        V.lemma_lower_sound n term lowered i (shift vs rho) target;
        FStar.Classical.excluded_middle (shift vs rho n == eval i lowered target);
        FStar.Classical.or_elim
          #(shift vs rho n == eval i lowered target)
          #(~(shift vs rho n == eval i lowered target))
          #(fun () -> lit_true i (shift vs rho) body <==> universal)
          (fun _ -> lemma_substitute_sound n lowered body i (shift vs rho) target)
          (fun _ -> lemma_guarded_outside universal n term body i (shift vs rho))
      in FStar.Classical.forall_intro aux)

let remove (n:nat) (term e:expr) : option expr =
  match e with
  | Quantifier k bs s body ->
    if (k = Forall_k || k = Exists_k) && s = bool_sort && get_sort body = bool_sort &&
       n < L.length (L.rev bs) && get_sort term = L.index (L.rev bs) n &&
       guarded (k = Forall_k) n term body then
      (match V.lower n term with
       | Some lowered ->
         let b = substitute n lowered body in
         if get_sort b = bool_sort
         then Some (V.quantified k (L.rev (V.erase n (L.rev bs))) b) else None
       | None -> None)
    else None
  | _ -> None

let lemma_remove_sound (n:nat) (term e result:expr)
                       (i:interpretation value) (rho:env value)
  : Lemma (requires B.boolean_rewrite_model i /\ eq_sound i /\ quant_extensional i /\
                    Q.quantifier_model i /\ remove n term e == Some result)
          (ensures eval i e rho == eval i result rho) =
  match e with
  | Quantifier k bs _ body ->
    let lowered = Some?.v (V.lower n term) in
    let bs' = L.rev (V.erase n (L.rev bs)) in
    FStar.List.Tot.Properties.rev_length bs;
    V.lemma_erase_length n (L.rev bs);
    FStar.List.Tot.Properties.rev_length (V.erase n (L.rev bs));
    lemma_assignments (k = Forall_k) n (L.length bs) term lowered body i rho;
    Q.lemma_quantifier_truth i rho k bs body;
    V.lemma_quantified_truth i rho k bs' (substitute n lowered body);
    match eval i e rho, eval i result rho with VBool _, VBool _ -> () | _, _ -> ()
  | _ -> ()

let endpoint (a b:expr) : list (nat & expr) =
  match a with Var n _ -> [(n, b)] | _ -> []

let rec candidates (e:expr) : Tot (list (nat & expr)) (decreases e) =
  match e with
  | Var n s -> if s = bool_sort then [(n, true_expr); (n, false_expr)] else []
  | App f args ->
    let here = match args with
      | [a; b] -> if f.decl_name = "=" then endpoint a b @ endpoint b a else []
      | _ -> [] in
    here @ candidates_args args
  | Quantifier _ _ _ _ -> []

and candidates_args (args:list expr) : Tot (list (nat & expr)) (decreases args) =
  match args with [] -> [] | a :: rest -> candidates a @ candidates_args rest

let rec first_removal (choices:list (nat & expr)) (e:expr)
  : Tot (option expr) (decreases choices) =
  match choices with
  | [] -> V.step e
  | (n, term) :: rest ->
    match remove n term e with Some result -> Some result | None -> first_removal rest e

let rec lemma_first_removal_sound (choices:list (nat & expr)) (e result:expr)
                                  (i:interpretation value) (rho:env value)
  : Lemma (requires B.boolean_rewrite_model i /\ eq_sound i /\ quant_extensional i /\
                    Q.quantifier_model i /\ first_removal choices e == Some result)
          (ensures eval i e rho == eval i result rho)
          (decreases choices) =
  match choices with
  | [] -> V.lemma_step_sound e result i rho
  | (n, term) :: rest ->
    match remove n term e with
    | Some _ -> lemma_remove_sound n term e result i rho
    | None -> lemma_first_removal_sound rest e result i rho

let step (e:expr) : option expr =
  match e with Quantifier _ _ _ body -> first_removal (candidates body) e | _ -> None

let lemma_step_sound (e result:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires B.boolean_rewrite_model i /\ eq_sound i /\ quant_extensional i /\
                    Q.quantifier_model i /\ step e == Some result)
          (ensures eval i e rho == eval i result rho) =
  match e with
  | Quantifier _ _ _ body -> lemma_first_removal_sound (candidates body) e result i rho
  | _ -> ()

let rec target_removal (choices:list (nat & expr)) (s t:expr)
  : Tot bool (decreases choices) =
  match choices with
  | [] -> false
  | (n, term) :: rest ->
    (match remove n term s with
     | Some result -> R.equivalent 64 result t || target_removal rest s t
     | None -> target_removal rest s t)

let rec lemma_target_removal (choices:list (nat & expr)) (s t:expr)
                             (i:interpretation value) (rho:env value)
  : Lemma (requires B.boolean_rewrite_model i /\ eq_sound i /\ quant_extensional i /\
                    Q.quantifier_model i /\ target_removal choices s t)
          (ensures eval i s rho == eval i t rho)
          (decreases choices) =
  match choices with
  | [] -> ()
  | (n, term) :: rest ->
    (match remove n term s with
     | Some result ->
       if R.equivalent 64 result t then (
         lemma_remove_sound n term s result i rho;
         R.lemma_equivalent 64 i rho result t)
       else lemma_target_removal rest s t i rho
     | None -> lemma_target_removal rest s t i rho)

let alternative_removal (s t:expr) : bool =
  match s with
  | Quantifier _ _ _ body -> target_removal (candidates body) s t
  | _ -> false

let lemma_alternative_removal (s t:expr) (i:interpretation value) (rho:env value)
  : Lemma (requires B.boolean_rewrite_model i /\ eq_sound i /\ quant_extensional i /\
                    Q.quantifier_model i /\ alternative_removal s t)
          (ensures eval i s rho == eval i t rho) =
  match s with
  | Quantifier _ _ _ body -> lemma_target_removal (candidates body) s t i rho
  | _ -> ()

let rec equivalent (fuel:nat) (s t:expr) : Tot bool (decreases %[fuel; 0]) =
  if s = t || B.boolean_equiv 8 10 s t then true
  else if fuel = 0 then false
  else let _ = assert (fuel > 0) in match step s, step t with
  | Some a, _ -> equivalent (fuel - 1) a t || alternative_removal s t
  | None, Some b -> equivalent (fuel - 1) s b || alternative_removal t s
  | None, None ->
    (match s, t with
     | App f xs, App g ys -> f = g && equivalent_args (fuel - 1) xs ys
     | Quantifier k bs q body, Quantifier k' bs' q' body' ->
       k = k' && bs = bs' && q = q' && equivalent (fuel - 1) body body'
     | _, _ -> false)

and equivalent_args (fuel:nat) (xs ys:list expr)
  : Tot bool (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: tail -> equivalent fuel x y && equivalent_args fuel rest tail
  | _, _ -> false

let rec lemma_equivalent_sound (fuel:nat) (s t:expr)
                               (i:interpretation value) (rho:env value)
  : Lemma (requires B.boolean_rewrite_model i /\ eq_sound i /\ quant_extensional i /\
                    Q.quantifier_model i /\ equivalent fuel s t)
          (ensures eval i s rho == eval i t rho)
          (decreases %[fuel; 0]) =
  if s = t then ()
  else if B.boolean_equiv 8 10 s t then B.lemma_boolean_equiv_sound 8 10 i rho s t
  else if fuel = 0 then ()
  else let _ = assert (fuel > 0) in match step s, step t with
  | Some a, _ ->
    if equivalent (fuel - 1) a t then (
      lemma_step_sound s a i rho;
      lemma_equivalent_sound (fuel - 1) a t i rho)
    else lemma_alternative_removal s t i rho
  | None, Some b ->
    if equivalent (fuel - 1) s b then (
      lemma_step_sound t b i rho;
      lemma_equivalent_sound (fuel - 1) s b i rho)
    else lemma_alternative_removal t s i rho
  | None, None ->
    (match s, t with
     | App _ xs, App _ ys -> lemma_equivalent_args_sound (fuel - 1) xs ys i rho
     | Quantifier _ bs _ body, Quantifier _ _ _ body' ->
       let aux (vs:list value{L.length vs = L.length bs})
         : Lemma (eval i body (shift vs rho) == eval i body' (shift vs rho)) =
         lemma_equivalent_sound (fuel - 1) body body' i (shift vs rho)
       in FStar.Classical.forall_intro aux
     | _, _ -> ())

and lemma_equivalent_args_sound (fuel:nat) (xs ys:list expr)
                                (i:interpretation value) (rho:env value)
  : Lemma (requires B.boolean_rewrite_model i /\ eq_sound i /\ quant_extensional i /\
                    Q.quantifier_model i /\ equivalent_args fuel xs ys)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | x :: rest, y :: tail ->
    lemma_equivalent_sound fuel x y i rho;
    lemma_equivalent_args_sound fuel rest tail i rho
  | _, _ -> ()
