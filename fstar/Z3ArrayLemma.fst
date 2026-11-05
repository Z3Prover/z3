module Z3ArrayLemma

open Z3AstTheory
open Z3ValueTheory
open Z3ProofTheory
open Z3ResolutionProofTheory
open Z3ObservationalEquality

let scalar_sort (s:sort) : bool =
  match s with BaseSort n -> n <> "Bool" | _ -> false

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

(* The existing value domain represents flat scalar arrays by Int -> Int.
   array-ext must carry the built-in operator tag, not merely its name.
   Its index must be a genuine difference witness, not an
   arbitrary index; Z3ArrayTheory proves such witnesses exist. *)
let array_model (i:interpretation value) : prop =
  (forall (f:func_decl) (a k:expr) (rho:env value).
    {:pattern (select_app f a k); (eval i a rho)}
    select_app f a k ==>
    (match eval i a rho, eval i k rho with
     | VArr av, VInt kv -> eval i (App f [a; k]) rho == VInt (Z3ArrayTheory.select av kv)
     | _, _ -> False)) /\
  (forall (f:func_decl) (a k v:expr) (rho:env value).
    {:pattern (store_app f a k v); (eval i a rho)}
    store_app f a k v ==>
    (match eval i a rho, eval i k rho, eval i v rho with
     | VArr av, VInt kv, VInt vv ->
       eval i (App f [a; k; v]) rho == VArr (Z3ArrayTheory.store av kv vv)
     | _, _, _ -> False)) /\
  (forall (f:func_decl) (a b:expr) (rho:env value).
    {:pattern (ext_app f a b); (eval i a rho)}
    ext_app f a b ==>
    (match eval i a rho, eval i b rho, eval i (App f [a; b]) rho with
     | VArr av, VArr bv, VInt kv -> Z3ArrayTheory.extensionality_index av bv kv
     | _, _, _ -> False))

#push-options "--fuel 4 --ifuel 2"

let lemma_select_parts (i:interpretation value) (rho:env value) (e a k:expr)
  : Lemma (requires array_model i /\ select_parts e == Some (a, k))
          (ensures (match eval i a rho, eval i k rho with
                    | VArr av, VInt kv -> eval i e rho == VInt (Z3ArrayTheory.select av kv)
                    | _, _ -> False))
  = match e with
    | App f [a'; k'] ->
      assert (a == a' /\ k == k' /\ select_app f a' k');
      assert (match eval i a' rho, eval i k' rho with
              | VArr av, VInt kv -> eval i (App f [a'; k']) rho == VInt (Z3ArrayTheory.select av kv)
              | _, _ -> False)
    | _ -> ()

let lemma_store_parts (i:interpretation value) (rho:env value) (e a k v:expr)
  : Lemma (requires array_model i /\ store_parts e == Some (a, k, v))
          (ensures (match eval i a rho, eval i k rho, eval i v rho with
                    | VArr av, VInt kv, VInt vv -> eval i e rho == VArr (Z3ArrayTheory.store av kv vv)
                    | _, _, _ -> False))
  = match e with
    | App f [a'; k'; v'] ->
      assert (a == a' /\ k == k' /\ v == v' /\ store_app f a' k' v')
    | _ -> ()

let lemma_ext_parts (i:interpretation value) (rho:env value) (e a b:expr)
  : Lemma (requires array_model i /\ ext_parts e == Some (a, b))
          (ensures (match eval i a rho, eval i b rho, eval i e rho with
                    | VArr av, VArr bv, VInt kv -> Z3ArrayTheory.extensionality_index av bv kv
                    | _, _, _ -> False))
  = match e with
    | App f [a'; b'] ->
      assert (a == a' /\ b == b' /\ ext_app f a' b')
    | _ -> ()

let lemma_equality_parts (i:interpretation value) (rho:env value) (e a b:expr)
  : Lemma (requires eq_sound i /\ equality_parts e == Some (a, b))
          (ensures lit_true i rho e <==> eval i a rho == eval i b rho)
  = match e with App _ [_; _] -> () | _ -> ()

let lemma_read_over_write_same (i:interpretation value) (rho:env value) (a b:expr)
  : Lemma (requires array_model i /\ read_over_write_same a b)
          (ensures eval i a rho == eval i b rho)
  = match select_parts a with
    | Some (s, k) ->
      (match store_parts s with
       | Some (base, index, v) ->
         lemma_store_parts i rho s base index v;
         lemma_select_parts i rho a s k;
         (match eval i base rho, eval i index rho, eval i v rho with
          | VArr av, VInt kv, VInt vv -> Z3ArrayTheory.lemma_select_store_same av kv vv
          | _, _, _ -> ())
       | None -> ())
    | None -> ()

let lemma_read_over_write_other (i:interpretation value) (rho:env value) (guard a b:expr)
  : Lemma (requires array_model i /\ eq_sound i /\ read_over_write_other guard a b)
          (ensures lit_true i rho guard \/ eval i a rho == eval i b rho)
  = match equality_parts guard, select_parts a, select_parts b with
    | Some (u, w), Some (s, k), Some (base, k') ->
      lemma_equality_parts i rho guard u w;
      (match store_parts s with
       | Some (base', index, v) ->
         lemma_store_parts i rho s base' index v;
         lemma_select_parts i rho a s k;
         lemma_select_parts i rho b base k';
         (match eval i base rho, eval i index rho, eval i k rho, eval i v rho with
          | VArr av, VInt iv, VInt kv, VInt vv -> Z3ArrayTheory.lemma_store_axiom2 av iv kv vv
          | _, _, _, _ -> ())
       | None -> ())
    | _, _, _ -> ()

let lemma_extensionality (i:interpretation value) (rho:env value) (a b x y:expr)
  : Lemma (requires array_model i /\ extensionality a b x y)
          (ensures eval i a rho == eval i b rho \/ ~(eval i x rho == eval i y rho))
  = match select_parts x, select_parts y with
    | Some (a', k), Some (b', k') ->
      lemma_select_parts i rho x a' k;
      lemma_select_parts i rho y b' k';
      (match ext_parts k with
       | Some (s, t) ->
         lemma_ext_parts i rho k s t;
         (match eval i s rho, eval i t rho, eval i k rho with
          | VArr av, VArr bv, VInt kv -> Z3ArrayTheory.lemma_extensionality_axiom av bv kv
          | _, _, _ -> ())
       | None -> ())
    | _, _ -> ()

let lemma_array_clause (i:interpretation value) (rho:env value) (p q:expr)
  : Lemma (requires array_model i /\ boolean_model i /\ eq_sound i /\ not_sound i /\ array_clause p q)
          (ensures lit_true i rho p \/ lit_true i rho q)
  = match equality_parts p, equality_parts q with
    | _, Some (a, b) ->
      lemma_equality_parts i rho q a b;
      if read_over_write_other p a b then lemma_read_over_write_other i rho p a b
      else lemma_read_over_write_other i rho p b a
    | Some (a, b), None ->
      lemma_equality_parts i rho p a b;
      (match q with
       | App f [negated] ->
         (match equality_parts negated with
          | Some (x, y) ->
            lemma_equality_parts i rho negated x y;
            (if extensionality a b x y then lemma_extensionality i rho a b x y
             else lemma_extensionality i rho b a x y);
            lemma_not_relates i rho f negated;
            (match eval i negated rho with VBool _ -> () | _ -> ())
          | None -> ())
       | _ -> ())

    | _, _ -> ()

let lemma_array_lemma_sound (i:interpretation value) (rho:env value) (e:expr)
  : Lemma (requires array_model i /\ boolean_model i /\ eq_sound i /\ not_sound i /\
                    or_sound i /\ array_lemma e)
          (ensures lit_true i rho e)
  = match equality_parts e with
    | Some (a, b) ->
      lemma_equality_parts i rho e a b;
      if read_over_write_same a b then lemma_read_over_write_same i rho a b
      else lemma_read_over_write_same i rho b a
    | None ->
      (match e with
       | App _ [p; q] ->
         if array_clause p q then lemma_array_clause i rho p q
         else lemma_array_clause i rho q p
       | _ -> ())

#pop-options
