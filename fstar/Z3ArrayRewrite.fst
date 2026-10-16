module Z3ArrayRewrite

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality
open Z3ArrayLemma
open Z3BooleanRewrite
module L = FStar.List.Tot

let term_ite_decl (s:sort) : func_decl =
  { decl_name = "if"; domain = [bool_sort; s; s]; range = s;
    interp = Some op_ite; int_params = [] }

let ite_parts (e:expr) : option (expr & expr & expr) =
  match e with
  | App f [c; t; u] ->
    if get_sort c = bool_sort && get_sort t = get_sort u &&
       f = term_ite_decl (get_sort t) then Some (c, t, u) else None
  | _ -> None

let term_ite_sound (i:interpretation value) : prop =
  forall (c t u:expr) (rho:env value).
    {:pattern (eval i (App (term_ite_decl (get_sort t)) [c; t; u]) rho)}
    get_sort c == bool_sort /\ get_sort t == get_sort u ==>
    eval i (App (term_ite_decl (get_sort t)) [c; t; u]) rho ==
      (if bool_value (eval i c rho) then eval i t rho else eval i u rho)

let rewrite_model (i:interpretation value) : prop =
  array_model i /\ boolean_rewrite_model i /\ term_ite_sound i

let store_contract (e:expr) : option expr =
  match e with
  | App f [a; k; v] ->
    if not (store_app f a k v) then None
    else (match store_parts a with
    | Some (base, j, _) ->
      if k = j then Some (App f [base; k; v])
      else if select_parts v = Some (a, k) then Some a else None
    | None -> if select_parts v = Some (a, k) then Some a else None)
  | _ -> None

let read_contract (e:expr) : option expr =
  match select_parts e with
  | Some (a, k) ->
    (match store_parts a with Some (_, j, v) -> if k = j then Some v else None
     | None -> None)
  | None -> None

let ite_contract (e:expr) : option expr =
  match ite_parts e with
  | Some (c, t, u) ->
    if c = true_expr || reflexive_equality c || t = u then Some t
    else if c = false_expr then Some u else None
  | None -> None

let contract (e:expr) : option expr =
  match store_contract e with
  | Some t -> Some t
  | None -> (match read_contract e with Some t -> Some t | None -> ite_contract e)

let expand_read (e:expr) : option expr =
  match e with
  | App f [a; k] ->
    if not (select_app f a k) then None
    else (match store_parts a with
    | Some (base, j, v) ->
      Some (App (term_ite_decl (get_sort v)) [mk_eq_expr j k; v; App f [base; k]])
    | None -> None)
  | _ -> None

#push-options "--fuel 4 --ifuel 2"

let lemma_ite_parts (i:interpretation value) (rho:env value) (e c t u:expr)
  : Lemma (requires term_ite_sound i /\ ite_parts e == Some (c, t, u))
          (ensures eval i e rho ==
                   (if bool_value (eval i c rho) then eval i t rho else eval i u rho))
  = match e with App _ [_; _; _] -> () | _ -> ()

let lemma_store_contract (i:interpretation value) (rho:env value) (e t:expr)
  : Lemma (requires array_model i /\ store_contract e == Some t)
          (ensures eval i e rho == eval i t rho)
  = match e with
    | App f [a; k; v] ->
      lemma_store_parts i rho e a k v;
      (match store_parts a with
       | Some (base, j, w) ->
         if k = j then (
           lemma_store_parts i rho a base j w;
           lemma_store_parts i rho (App f [base; k; v]) base k v;
           match eval i base rho, eval i k rho, eval i w rho, eval i v rho with
           | VArr av, VInt kv, VInt wv, VInt vv ->
             Z3ArrayTheory.lemma_store_same_twice av kv wv vv
           | _, _, _, _ -> ())
         else (
           lemma_select_parts i rho v a k;
           match eval i a rho, eval i k rho with
           | VArr av, VInt kv -> Z3ArrayTheory.lemma_store_redundant av kv
           | _, _ -> ())
       | None ->
         lemma_select_parts i rho v a k;
         (match eval i a rho, eval i k rho with
          | VArr av, VInt kv -> Z3ArrayTheory.lemma_store_redundant av kv
          | _, _ -> ()))
    | _ -> ()

let lemma_read_contract (i:interpretation value) (rho:env value) (e t:expr)
  : Lemma (requires array_model i /\ read_contract e == Some t)
          (ensures eval i e rho == eval i t rho)
  = assert (read_over_write_same e t);
    lemma_read_over_write_same i rho e t

let lemma_ite_contract (i:interpretation value) (rho:env value) (e t:expr)
  : Lemma (requires rewrite_model i /\ ite_contract e == Some t)
          (ensures eval i e rho == eval i t rho)
  = match ite_parts e with
    | Some (c, a, b) ->
      lemma_ite_parts i rho e c a b;
      if reflexive_equality c then
        (match c with App _ [_; _] -> () | _ -> ())
    | None -> ()

let lemma_contract (i:interpretation value) (rho:env value) (e t:expr)
  : Lemma (requires rewrite_model i /\ contract e == Some t)
          (ensures eval i e rho == eval i t rho)
  = match store_contract e with
    | Some _ -> lemma_store_contract i rho e t
    | None ->
      (match read_contract e with
       | Some _ -> lemma_read_contract i rho e t
       | None -> lemma_ite_contract i rho e t)

let lemma_expand_read (i:interpretation value) (rho:env value) (e t:expr)
  : Lemma (requires rewrite_model i /\ expand_read e == Some t)
          (ensures eval i e rho == eval i t rho)
  = match e with
    | App f [a; k] ->
      (match store_parts a with
       | Some (base, j, v) ->
         lemma_store_parts i rho a base j v;
         lemma_select_parts i rho e a k;
         lemma_select_parts i rho (App f [base; k]) base k;
         lemma_equality_parts i rho (mk_eq_expr j k) j k;
         lemma_ite_parts i rho t (mk_eq_expr j k) v (App f [base; k]);
         (match eval i base rho, eval i j rho, eval i k rho, eval i v rho with
          | VArr av, VInt jv, VInt kv, VInt vv ->
            if jv = kv then Z3ArrayTheory.lemma_select_store_same av jv vv
            else Z3ArrayTheory.lemma_select_store_diff av jv kv vv
          | _, _, _, _ -> ())
       | None -> ())
    | _ -> ()

#pop-options

let rec equivalent (fuel:nat) (s t:expr)
  : Tot bool (decreases %[fuel; 0]) =
  if s = t then true
  else if fuel = 0 || get_sort s <> get_sort t then false
  else match contract s, contract t with
  | Some a, _ -> equivalent (fuel - 1) a t
  | None, Some b -> equivalent (fuel - 1) s b
  | None, None ->
    let congruent =
      match s, t with
      | App f xs, App g ys -> f = g && equivalent_args (fuel - 1) xs ys
      | _, _ -> false in
    if congruent then true
    else
      let symmetric =
        match equality_parts s, equality_parts t with
        | Some (a, b), Some (c, d) ->
          equivalent (fuel - 1) a d && equivalent (fuel - 1) b c
        | _, _ -> false in
      if symmetric then true
      else match expand_read s, expand_read t with
      | Some a, _ -> equivalent (fuel - 1) a t
      | None, Some b -> equivalent (fuel - 1) s b
      | None, None ->
        (match ite_parts s, ite_parts t with
         | Some (_, a, b), _ ->
           equivalent (fuel - 1) a t && equivalent (fuel - 1) b t
         | None, Some (_, a, b) ->
           equivalent (fuel - 1) s a && equivalent (fuel - 1) s b
         | None, None -> false)

and equivalent_args (fuel:nat) (xs ys:list expr)
  : Tot bool (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | [], [] -> true
  | x :: rest, y :: rest' -> equivalent fuel x y && equivalent_args fuel rest rest'
  | _, _ -> false

let rec lemma_equivalent_sound (fuel:nat) (i:interpretation value) (rho:env value)
                               (s t:expr)
  : Lemma (requires rewrite_model i /\ equivalent fuel s t)
          (ensures eval i s rho == eval i t rho)
          (decreases %[fuel; 0]) =
  if s = t || fuel = 0 then ()
  else match contract s, contract t with
  | Some a, _ ->
    lemma_contract i rho s a;
    lemma_equivalent_sound (fuel - 1) i rho a t
  | None, Some b ->
    lemma_contract i rho t b;
    lemma_equivalent_sound (fuel - 1) i rho s b
  | None, None ->
    let congruent =
      match s, t with
      | App f xs, App g ys -> f = g && equivalent_args (fuel - 1) xs ys
      | _, _ -> false in
    if congruent then (
      match s, t with
      | App _ xs, App _ ys -> lemma_equivalent_args_sound (fuel - 1) i rho xs ys
      | _, _ -> ())
    else
      let symmetric =
        match equality_parts s, equality_parts t with
        | Some (a, b), Some (c, d) ->
          equivalent (fuel - 1) a d && equivalent (fuel - 1) b c
        | _, _ -> false in
      if symmetric then (
        match equality_parts s, equality_parts t with
        | Some (a, b), Some (c, d) ->
          lemma_equivalent_sound (fuel - 1) i rho a d;
          lemma_equivalent_sound (fuel - 1) i rho b c;
          lemma_equality_parts i rho s a b;
          lemma_equality_parts i rho t c d;
          (match eval i s rho, eval i t rho with VBool _, VBool _ -> () | _, _ -> ())
        | _, _ -> ())
      else match expand_read s, expand_read t with
      | Some a, _ ->
        lemma_expand_read i rho s a;
        lemma_equivalent_sound (fuel - 1) i rho a t
      | None, Some b ->
        lemma_expand_read i rho t b;
        lemma_equivalent_sound (fuel - 1) i rho s b
      | None, None ->
        (match ite_parts s, ite_parts t with
         | Some (c, a, b), _ ->
           lemma_ite_parts i rho s c a b;
           lemma_equivalent_sound (fuel - 1) i rho a t;
           lemma_equivalent_sound (fuel - 1) i rho b t
         | None, Some (c, a, b) ->
           lemma_ite_parts i rho t c a b;
           lemma_equivalent_sound (fuel - 1) i rho s a;
           lemma_equivalent_sound (fuel - 1) i rho s b
         | None, None -> ())

and lemma_equivalent_args_sound (fuel:nat) (i:interpretation value) (rho:env value)
                                (xs ys:list expr)
  : Lemma (requires rewrite_model i /\ equivalent_args fuel xs ys)
          (ensures eval_args i xs rho == eval_args i ys rho)
          (decreases %[fuel; L.length xs + 1]) =
  match xs, ys with
  | x :: rest, y :: rest' ->
    lemma_equivalent_sound fuel i rho x y;
    lemma_equivalent_args_sound fuel i rho rest rest'
  | _, _ -> ()
