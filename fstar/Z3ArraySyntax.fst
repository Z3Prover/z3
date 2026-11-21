module Z3ArraySyntax

open Z3AstTheory
open Z3OperatorTags
open Z3ClauseSyntax
open Z3BooleanRewriteSyntax
module L = FStar.List.Tot

let scalar_sort (s:sort) : bool =
  s <> bool_sort && (match s with BaseSort _ | SortApp _ [] -> true | _ -> false)

let select_app (f:func_decl) (a k:expr) : bool =
  match get_sort a with
  | ArraySort [index] element ->
    scalar_sort index && scalar_sort element && get_sort k = index &&
    f = { decl_name = "select"; domain = [get_sort a; index]; range = element;
          interp = Some op_select; int_params = [] }
  | _ -> false

let store_app (f:func_decl) (a k v:expr) : bool =
  match get_sort a with
  | ArraySort [index] element ->
    scalar_sort index && scalar_sort element && get_sort k = index && get_sort v = element &&
    f = { decl_name = "store"; domain = [get_sort a; index; element]; range = get_sort a;
          interp = Some op_store; int_params = [] }
  | _ -> false

let ext_app (f:func_decl) (a b:expr) : bool =
  match get_sort a with
  | ArraySort [index] element ->
    scalar_sort index && scalar_sort element && get_sort b = get_sort a &&
    f = { decl_name = "array-ext"; domain = [get_sort a; get_sort a]; range = index;
          interp = Some op_array_ext; int_params = [] }
  | _ -> false

let select_parts (e:expr) : option (expr & expr) =
  match e with App f [a; k] -> if select_app f a k then Some (a, k) else None | _ -> None

let store_parts (e:expr) : option (expr & expr & expr) =
  match e with App f [a; k; v] -> if store_app f a k v then Some (a, k, v) else None | _ -> None

let ext_parts (e:expr) : option (expr & expr) =
  match e with App f [a; b] -> if ext_app f a b then Some (a, b) else None | _ -> None

let equality_parts (e:expr) : option (expr & expr) =
  match e with
  | App f [a; b] ->
    if get_sort a = get_sort b && f = eq_decl (get_sort a) then Some (a, b) else None
  | _ -> None

let same_indices (a b x y:expr) : bool = (a = x && b = y) || (a = y && b = x)

let read_over_write_same (a b:expr) : bool =
  match select_parts a with
  | Some (s, k) ->
    (match store_parts s with Some (_, j, v) -> k = j && b = v | None -> false)
  | None -> false

let read_over_write_other (guard a b:expr) : bool =
  match equality_parts guard, select_parts a, select_parts b with
  | Some (i, j), Some (s, k), Some (base, k') ->
    (match store_parts s with
     | Some (base', index, _) -> base = base' && k = k' && same_indices i j index k
     | None -> false)
  | _, _, _ -> false

let extensionality (a b x y:expr) : bool =
  match select_parts x, select_parts y with
  | Some (a', k), Some (b', k') ->
    a = a' && b = b' && k = k' &&
    (match ext_parts k with Some (s, t) -> same_indices s t a b | None -> false)
  | _, _ -> false

let array_clause (p q:expr) : bool =
  match equality_parts p, equality_parts q with
  | _, Some (a, b) -> read_over_write_other p a b || read_over_write_other p b a
  | Some (a, b), None ->
    (match q with
     | App f [negated] ->
       if f = { decl_name = "not"; domain = [bool_sort]; range = bool_sort;
                interp = Some op_not; int_params = [] } then
         (match equality_parts negated with
          | Some (x, y) -> extensionality a b x y || extensionality b a x y
          | None -> false)
       else false
     | _ -> false)
  | _, _ -> false

let array_lemma (e:expr) : bool =
  match equality_parts e with
  | Some (a, b) -> read_over_write_same a b || read_over_write_same b a
  | None ->
    (match e with
     | App f [p; q] ->
       f = { decl_name = "or"; domain = [bool_sort; bool_sort]; range = bool_sort;
             interp = Some op_or; int_params = [] } &&
       (array_clause p q || array_clause q p)
     | _ -> false)

let const_array (f:func_decl) (v:expr) : bool =
  match f.range with
  | ArraySort bs element ->
    bs <> [] && element = get_sort v &&
    f = { decl_name = "const"; domain = [element]; range = ArraySort bs element;
          interp = Some op_const_array; int_params = [] }
  | _ -> false

let select_decl (f:func_decl) (array:expr) (args:list expr) : bool =
  match get_sort array with
  | ArraySort bs element ->
    sorts_match args bs &&
    f = { decl_name = "select"; domain = get_sort array :: bs; range = element;
          interp = Some op_select; int_params = [] }
  | _ -> false


let term_ite_decl (s:sort) : func_decl =
  { decl_name = "if"; domain = [bool_sort; s; s]; range = s;
    interp = Some op_ite; int_params = [] }

let ite_parts (e:expr) : option (expr & expr & expr) =
  match e with
  | App f [c; t; u] ->
    if get_sort c = bool_sort && get_sort t = get_sort u &&
       f = term_ite_decl (get_sort t) then Some (c, t, u) else None
  | _ -> None

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

let ite_merge (e:expr) : option expr =
  match ite_parts e with
  | Some (c, t, u) ->
    (match ite_parts u with
    | Some (d, a, b) ->
      if t = a then
        let condition = App (connective_decl Disjunction [c; d]) [c; d] in
        Some (App (term_ite_decl (get_sort t)) [condition; t; b])
      else None
    | None ->
      (match ite_parts t with
       | Some (d, a, b) ->
         if u = b then
           let condition = App (connective_decl Conjunction [c; d]) [c; d] in
           Some (App (term_ite_decl (get_sort a)) [condition; a; u])
         else None
       | None -> None))
  | None -> None

let ite_equivalent (s t:expr) : bool =
  match ite_parts s, ite_parts t with
  | Some (c, a, b), Some (d, u, v) ->
    (a = u && b = v && boolean_equiv 8 10 c d) ||
    (a = v && b = u &&
     (c = mk_not_expr d || d = mk_not_expr c || boolean_equiv 8 10 c (mk_not_expr d)))
  | _, _ -> false

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

let rec equivalent (fuel:nat) (s t:expr)
  : Tot bool (decreases %[fuel; 0]) =
  if s = t then true
  else if fuel = 0 || get_sort s <> get_sort t then false
  else let _ = assert (fuel > 0) in
  if ite_equivalent s t then true
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
        let merged =
          match ite_merge s, ite_merge t with
          | Some a, _ -> equivalent (fuel - 1) a t
          | None, Some b -> equivalent (fuel - 1) s b
          | None, None -> false in
        if merged then true else
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

let lemma_other_indices (guard a b u w stored k base k' original j v:expr)
  : Lemma (requires read_over_write_other guard a b /\
                    equality_parts guard == Some (u, w) /\
                    select_parts a == Some (stored, k) /\
                    select_parts b == Some (base, k') /\
                    store_parts stored == Some (original, j, v))
          (ensures base == original /\ k == k' /\ same_indices u w j k) = ()
