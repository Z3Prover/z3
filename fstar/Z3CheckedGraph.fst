(*
   Z3CheckedGraph.fst

   A document-local graph of the reflected expressions a checker consumes,
   built while they are marshaled, so that an expression shared by the
   reflected AST is one node however often it occurs. Each node `x` stores
   its exact expression (`value_of g x`) next to the scope-shape node that
   `Z3CheckedTerms.represents` reads, and `graph_inv` states that every stored
   expression is the constructor of its node applied to its children's stored
   expressions and to sorts given by checked sort ids:

   * a variable: `Var n s` with the checked id of `s`;
   * an application: `App f args`, `args` the stored expressions of earlier
     child nodes, `f.range` and the declaration's domain given by checked ids,
     and the scope-independent result `sorts_match args f.domain` decided by
     comparing ids (sort equality, `Z3CheckedSorts.lemma_id_equal`);
   * a quantifier: `Quantifier k bs q b`, `bs` given by checked ids, `b` the
     stored expression of an earlier node, `q` the sort the quantifier has.

   The builders are the only way nodes are added; each takes the nodes and
   checked sorts of the children, reads their stored expressions (never
   comparing expressions), and returns the new node. A node id is
   an index into this graph, valid only with it: it stands for no expression
   equality across nodes or graphs, and native ids are not node ids.
   `lemma_represents`: a node of an invariant graph represents its stored
   expression, which is what the scope checks read.

   Units, charged before the step they pay for, from the graph's own
   Preparation and Storage budgets. Preparation: one per child read or
   compared and `2 table_units` per child (its node and expression looked
   up), `2 table_units` to store a node and its expression, and the units of
   `Z3CheckedSorts` interning (names counted by the bounded counter, bucket
   comparisons, table updates). Storage: `2 (1 + table_units)` per node (the
   node, its expression cell and two copied tree paths), one cell per child
   in the node, two per child for the accumulated lists of expressions and
   sort ids, and the cells of interning. The units are an abstract count,
   not a time or memory bound.
*)
module Z3CheckedGraph

open Z3AstTheory
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module T = Z3CheckedTerms

(* A reflected sort and its checked id. *)
type csort = sort & nat

noeq
type cgraph = {
  terms: T.term_graph;
  values: I.index_tree expr;
  prep: nat;
  store: nat;
}

let empty (prep store:nat) : cgraph = { terms = T.empty_graph; values = I.Empty; prep = prep; store = store }

let node_count (g:cgraph) : nat = g.terms.T.expr_count

let sort_count (g:cgraph) : nat = g.terms.T.sorts.CS.node_count

let value_of (g:cgraph) (x:nat) : option expr = I.index_get g.values x

let node_of (g:cgraph) (x:nat) : option T.enode = T.expr_node g.terms x

let enode_sort (n:T.enode) : nat =
  match n with
  | T.ENVar _ i -> i
  | T.ENApp _ _ i -> i
  | T.ENQuant _ _ _ i -> i

unfold noextract
let interp (g:cgraph) : nat -> sort = CS.interp_node g.terms.T.sorts

let csort_ok (g:cgraph) (c:csort) : prop = snd c < sort_count g /\ interp g (snd c) == fst c

noextract
let rec csorts_ok (g:cgraph) (cs:list csort) : Tot prop (decreases cs) =
  match cs with
  | [] -> True
  | c :: rest -> csort_ok g c /\ csorts_ok g rest

noextract
let rec values_of (g:cgraph) (xs:list nat) : Tot (option (list expr)) (decreases xs) =
  match xs with
  | [] -> Some []
  | x :: rest ->
    (match value_of g x, values_of g rest with
     | Some v, Some vs -> Some (v :: vs)
     | _, _ -> None)

[@@"opaque_to_smt"]
noextract
let node_exact (g:cgraph) (x:nat) : prop =
  match node_of g x, value_of g x with
  | Some (T.ENVar m i), Some (Var n s) -> m == n /\ i < sort_count g /\ interp g i == s
  | Some (T.ENApp ok xs i), Some (App f args) ->
    CS.all_below xs x /\ values_of g xs == Some args /\ i < sort_count g /\ interp g i == f.range /\
    ok == sorts_match args f.domain
  | Some (T.ENQuant ok ys y i), Some (Quantifier k bs q b) ->
    CS.all_below ys (sort_count g) /\ L.map (interp g) ys == bs /\ i < sort_count g /\ interp g i == q /\
    ok == (q = quant_sort k bs (get_sort b) && (k = Lambda_k || get_sort b = bool_sort)) /\
    y < x /\ value_of g y == Some b
  | _, _ -> False

let reveal_exact (g:cgraph) (x:nat) : Lemma (node_exact g x == (match node_of g x, value_of g x with
  | Some (T.ENVar m i), Some (Var n s) -> m == n /\ i < sort_count g /\ interp g i == s
  | Some (T.ENApp ok xs i), Some (App f args) ->
    CS.all_below xs x /\ values_of g xs == Some args /\ i < sort_count g /\ interp g i == f.range /\
    ok == sorts_match args f.domain
  | Some (T.ENQuant ok ys y i), Some (Quantifier k bs q b) ->
    CS.all_below ys (sort_count g) /\ L.map (interp g) ys == bs /\ i < sort_count g /\ interp g i == q /\
    ok == (q = quant_sort k bs (get_sort b) && (k = Lambda_k || get_sort b = bool_sort)) /\
    y < x /\ value_of g y == Some b
  | _, _ -> False))
  = FStar.Pervasives.reveal_opaque (`%node_exact) (node_exact g x)

let graph_inv (g:cgraph) : prop =
  T.graph_ok g.terms /\ (forall (x:nat). x < node_count g ==> node_exact g x)

(* `g'` extends `g`: earlier nodes, expressions and sort ids are unchanged. *)
let cgrows (g g':cgraph) : prop =
  T.graph_grows g.terms g'.terms /\
  (forall (x:nat). x < node_count g ==> value_of g' x == value_of g x)

let lemma_cgrows_refl (g:cgraph) : Lemma (cgrows g g) = ()

let lemma_cgrows_trans (g1 g2 g3:cgraph)
  : Lemma (requires cgrows g1 g2 /\ cgrows g2 g3) (ensures cgrows g1 g3)
  = ()

(* --- Extensions keep every earlier fact -------------------------------------------------------- *)

let lemma_csort_grows (g g':cgraph) (c:csort)
  : Lemma (requires cgrows g g' /\ csort_ok g c) (ensures csort_ok g' c)
  = CS.lemma_interp_agree g.terms.T.sorts g'.terms.T.sorts (sort_count g) (snd c)

let rec lemma_csorts_grows (g g':cgraph) (cs:list csort)
  : Lemma (requires cgrows g g' /\ csorts_ok g cs) (ensures csorts_ok g' cs) (decreases cs)
  = match cs with
    | [] -> ()
    | c :: rest -> lemma_csort_grows g g' c; lemma_csorts_grows g g' rest

let rec lemma_values_of_grows (g g':cgraph) (xs:list nat)
  : Lemma (requires cgrows g g' /\ CS.all_below xs (node_count g))
          (ensures values_of g' xs == values_of g xs) (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: rest -> lemma_values_of_grows g g' rest

let lemma_quant_exact_grows (g g':cgraph) (x:nat) (ok:bool) (ys:list nat) (y i:nat)
                            (k:quantifier_kind) (bs:list sort) (q:sort) (b:expr)
  : Lemma (requires cgrows g g' /\ x < node_count g /\ node_of g x == Some (T.ENQuant ok ys y i) /\
                    value_of g x == Some (Quantifier k bs q b) /\ node_exact g x)
          (ensures node_exact g' x)
  = reveal_exact g x; reveal_exact g' x;
    let t = g.terms.T.sorts in
    let t' = g'.terms.T.sorts in
    let n = sort_count g in
    assert (CS.all_below ys n /\ L.map (interp g) ys == bs /\ i < n /\ interp g i == q /\ y < x /\
            value_of g y == Some b);
    CS.lemma_interp_agree t t' n i;
    CS.lemma_map_agree t t' n ys;
    T.lemma_all_below_widen ys n (sort_count g');
    assert (node_of g' x == node_of g x);
    assert (value_of g' x == value_of g x);
    assert (value_of g' y == value_of g y)

let lemma_node_exact_grows (g g':cgraph) (x:nat)
  : Lemma (requires cgrows g g' /\ x < node_count g /\ node_exact g x) (ensures node_exact g' x)
  = reveal_exact g x; reveal_exact g' x;
    let t = g.terms.T.sorts in
    let t' = g'.terms.T.sorts in
    let n = sort_count g in
    match node_of g x, value_of g x with
    | Some (T.ENVar _ i), Some (Var _ _) -> CS.lemma_interp_agree t t' n i
    | Some (T.ENApp _ xs i), Some (App _ _) ->
      CS.lemma_interp_agree t t' n i;
      T.lemma_all_below_widen xs x (node_count g);
      lemma_values_of_grows g g' xs
    | Some (T.ENQuant ok ys y i), Some (Quantifier k bs q b) ->
      lemma_quant_exact_grows g g' x ok ys y i k bs q b
    | _, _ -> ()

(* --- What an invariant graph earns --------------------------------------------------------------- *)

let lemma_node_sort (g:cgraph) (x:nat)
  : Lemma (requires graph_inv g /\ x < node_count g)
          (ensures (match node_of g x, value_of g x with
                    | Some n, Some v -> enode_sort n < sort_count g /\ interp g (enode_sort n) == get_sort v
                    | _, _ -> False))
  = assert (node_exact g x); reveal_exact g x

let rec lemma_represents (g:cgraph) (x:nat) (e:expr)
  : Lemma (requires graph_inv g /\ x < node_count g /\ value_of g x == Some e)
          (ensures T.represents g.terms x e) (decreases e)
  = assert (node_exact g x); reveal_exact g x;
    match e, node_of g x with
    | App _ args, Some (T.ENApp _ xs _) ->
      T.lemma_all_below_widen xs x (node_count g);
      lemma_represents_list g xs args
    | Quantifier _ _ _ b, Some (T.ENQuant _ _ y _) -> lemma_represents g y b
    | _, _ -> ()

and lemma_represents_list (g:cgraph) (xs:list nat) (args:list expr)
  : Lemma (requires graph_inv g /\ CS.all_below xs (node_count g) /\ values_of g xs == Some args)
          (ensures T.represents_list g.terms xs args) (decreases args)
  = match xs, args with
    | x :: xs', a :: args' -> lemma_represents g x a; lemma_represents_list g xs' args'
    | _, _ -> ()

(* --- Storing a node ------------------------------------------------------------------------------- *)

noeq
type built =
  | Built : graph:cgraph -> node:nat -> built
  | BuildExhausted : phase:T.phase -> built
  | BuildInvalid

let node_units : nat = 2 * CS.table_units

let node_cells (children:nat) : nat = 2 * (1 + CS.table_units) + children

(* The next node, `n` with expression `v`, paid from `prep` and `store`. *)
let put_node (g:cgraph) (n:T.enode) (v:expr) (children prep store:nat) : built =
  if prep < node_units then BuildExhausted T.Preparation
  else if store < node_cells children || node_count g >= T.max_expr_nodes then BuildExhausted T.Storage
  else
    let x = node_count g in
    Built ({ terms = { g.terms with T.expr_nodes = I.index_put g.terms.T.expr_nodes x n; T.expr_count = x + 1 };
             values = I.index_put g.values x v;
             prep = prep - node_units; store = store - node_cells children }) x

let put_ok (g:cgraph) (n:T.enode) (v:expr) (r:built) : prop =
  match r with
  | Built g' x ->
    x == node_count g /\ node_count g' == x + 1 /\ g'.terms.T.sorts == g.terms.T.sorts /\ cgrows g g' /\
    node_of g' x == Some n /\ value_of g' x == Some v
  | _ -> True

let lemma_put_node (g:cgraph) (n:T.enode) (v:expr) (children prep store:nat)
  : Lemma (put_ok g n v (put_node g n v children prep store))
  = match put_node g n v children prep store with
    | Built g' x ->
      let aux (y:nat) : Lemma (node_of g' y == (if y = x then Some n else node_of g y) /\
                               value_of g' y == (if y = x then Some v else value_of g y))
        = I.lemma_index_put g.terms.T.expr_nodes x n y; I.lemma_index_put g.values x v y in
      FStar.Classical.forall_intro aux
    | _ -> ()

(* An invariant graph stays invariant when the new node is exact. *)
let lemma_put_inv (g:cgraph) (n:T.enode) (v:expr) (g':cgraph) (x:nat)
  : Lemma (requires graph_inv g /\ put_ok g n v (Built g' x) /\ node_exact g' x)
          (ensures graph_inv g')
  = assert (x == node_count g /\ node_count g' == x + 1 /\ cgrows g g');
    let aux (y:nat) : Lemma (requires y < node_count g') (ensures node_exact g' y)
        = if y < x then begin
            assert (node_exact g y);
            lemma_node_exact_grows g g' y
          end else assert (y == x) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    assert (T.graph_ok g'.terms)

(* --- Reading children -------------------------------------------------------------------------- *)

noeq
type children_read =
  | ChildrenRead : values:list expr -> sorts:list nat -> prep:nat -> store:nat -> children_read
  | ChildrenExhausted : phase:T.phase -> children_read
  | ChildrenInvalid

let child_units : nat = 1 + 2 * CS.table_units

(* The stored expressions and sort ids of `xs`, accumulated last first. *)
let rec read_children (g:cgraph) (xs:list nat) (vs:list expr) (ss:list nat) (prep store:nat)
  : Tot children_read (decreases xs) =
  match xs with
  | [] -> ChildrenRead (L.rev vs) (L.rev ss) prep store
  | x :: rest ->
    if prep < child_units then ChildrenExhausted T.Preparation
    else if store < 2 then ChildrenExhausted T.Storage
    else if x >= node_count g then ChildrenInvalid
    else
      match node_of g x, value_of g x with
      | Some n, Some v -> read_children g rest (v :: vs) (enode_sort n :: ss) (prep - child_units) (store - 2)
      | _, _ -> ChildrenInvalid

let rec lemma_map_rev (#a #b:Type) (f:a -> b) (l:list a)
  : Lemma (ensures L.map f (L.rev l) == L.rev (L.map f l)) (decreases l)
  = match l with
    | [] -> ()
    | x :: rest ->
      lemma_map_rev f rest;
      Z3List.lemma_rev_cons x rest;
      Z3List.lemma_rev_cons (f x) (L.map f rest);
      FStar.List.Tot.Properties.map_append f (L.rev rest) [x]

noextract
let read_ok (g:cgraph) (xs:list nat) (r:children_read) : prop =
  match r with
  | ChildrenRead vs ss prep _ ->
    values_of g xs == Some vs /\ CS.all_below xs (node_count g) /\ CS.all_below ss (sort_count g) /\
    L.map (interp g) ss == L.map get_sort vs /\ L.length vs == L.length xs
  | _ -> True

let rec lemma_read_children (g:cgraph) (xs:list nat) (vs:list expr) (ss:list nat) (prep store:nat)
  : Lemma (requires graph_inv g /\ CS.all_below ss (sort_count g) /\ L.map (interp g) ss == L.map get_sort vs /\
                    L.length ss == L.length vs)
          (ensures (match read_children g xs vs ss prep store with
                    | ChildrenRead vs' ss' p _ ->
                      p <= prep /\
                      (exists (args:list expr). values_of g xs == Some args /\ vs' == L.append (L.rev vs) args) /\
                      CS.all_below xs (node_count g) /\ CS.all_below ss' (sort_count g) /\
                      L.map (interp g) ss' == L.map get_sort vs' /\
                      L.length vs' == L.length vs + L.length xs
                    | _ -> True))
          (decreases xs)
  = match xs with
    | [] ->
      FStar.List.Tot.Properties.rev_length vs;
      FStar.List.Tot.Properties.rev_length ss;
      lemma_map_rev (interp g) ss;
      lemma_map_rev get_sort vs;
      T.lemma_all_below_rev ss (sort_count g);
      FStar.List.Tot.Properties.append_l_nil (L.rev vs)
    | x :: rest ->
      if prep < child_units || store < 2 || x >= node_count g then ()
      else
        match node_of g x, value_of g x with
        | Some n, Some v ->
          begin
            lemma_node_sort g x;
            lemma_read_children g rest (v :: vs) (enode_sort n :: ss) (prep - child_units) (store - 2);
            match read_children g rest (v :: vs) (enode_sort n :: ss) (prep - child_units) (store - 2) with
            | ChildrenRead vs' _ _ _ ->
              Z3List.lemma_rev_cons v vs;
              let aux (args:list expr)
                : Lemma (requires values_of g rest == Some args /\ vs' == L.append (L.rev (v :: vs)) args)
                        (ensures values_of g xs == Some (v :: args) /\ vs' == L.append (L.rev vs) (v :: args))
                = FStar.List.Tot.Properties.append_assoc (L.rev vs) [v] args in
              FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
            | _ -> ()
          end
        | _, _ -> ()

let lemma_read_children_ok (g:cgraph) (xs:list nat) (prep store:nat)
  : Lemma (requires graph_inv g) (ensures read_ok g xs (read_children g xs [] [] prep store))
  = lemma_read_children g xs [] [] prep store

(* --- Builders ------------------------------------------------------------------------------------- *)

(* A base sort, interned by its exact name. *)
noeq
type sorted =
  | Sorted : graph:cgraph -> sort:csort -> sorted
  | SortExhausted : phase:T.phase -> sorted

let with_sorts (g:cgraph) (t:CS.sort_table) (prep store:nat) : cgraph =
  { g with terms = { g.terms with T.sorts = t }; prep = prep; store = store }

let base_sort (g:cgraph) (name:string) : sorted =
  match T.intern_base g.terms.T.sorts name g.prep g.store with
  | CS.InternExhausted p -> SortExhausted (T.sort_phase p)
  | CS.Interned t c w s -> Sorted (with_sorts g t w s) (BaseSort name, c)

let array_sort (g:cgraph) (ds:list csort) (r:csort) : sorted =
  let ids = L.map snd ds in
  match T.intern_array g.terms.T.sorts ids (L.length ids) (snd r) g.prep g.store with
  | CS.InternExhausted p -> SortExhausted (T.sort_phase p)
  | CS.Interned t c w s -> Sorted (with_sorts g t w s) (ArraySort (L.map fst ds) (fst r), c)

let sorted_ok (g:cgraph) (r:sorted) : prop =
  match r with
  | Sorted g' c -> graph_inv g' /\ cgrows g g' /\ csort_ok g' c /\ node_count g' == node_count g
  | SortExhausted _ -> True

let lemma_with_sorts (g:cgraph) (t:CS.sort_table) (prep store:nat)
  : Lemma (requires graph_inv g /\ CS.valid_table t /\ T.table_grows g.terms.T.sorts t)
          (ensures graph_inv (with_sorts g t prep store) /\ cgrows g (with_sorts g t prep store))
  = let g' = with_sorts g t prep store in
    let aux (y:nat) : Lemma (requires y < node_count g') (ensures node_exact g' y)
      = lemma_node_exact_grows g g' y in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let lemma_base_sort (g:cgraph) (name:string)
  : Lemma (requires graph_inv g) (ensures sorted_ok g (base_sort g name))
  = T.lemma_intern_base g.terms.T.sorts name g.prep g.store;
    match T.intern_base g.terms.T.sorts name g.prep g.store with
    | CS.Interned t c w s -> lemma_with_sorts g t w s; CS.lemma_interp_node t c
    | _ -> ()

let rec lemma_csorts_ids (g:cgraph) (ds:list csort)
  : Lemma (requires csorts_ok g ds)
          (ensures CS.all_below (L.map snd ds) (sort_count g) /\ L.map (interp g) (L.map snd ds) == L.map fst ds)
          (decreases ds)
  = match ds with [] -> () | _ :: rest -> lemma_csorts_ids g rest

let lemma_array_sort (g:cgraph) (ds:list csort) (r:csort)
  : Lemma (requires graph_inv g /\ csorts_ok g ds /\ csort_ok g r) (ensures sorted_ok g (array_sort g ds r))
  = let ids = L.map snd ds in
    let t = g.terms.T.sorts in
    lemma_csorts_ids g ds;
    T.lemma_intern_array t ids (L.length ids) (snd r) g.prep g.store;
    match T.intern_array t ids (L.length ids) (snd r) g.prep g.store with
    | CS.Interned t' c w s ->
      let g' = with_sorts g t' w s in
      lemma_with_sorts g t' w s;
      CS.lemma_interp_node t' c;
      CS.lemma_map_agree t t' (sort_count g) ids;
      CS.lemma_interp_agree t t' (sort_count g) (snd r);
      assert (CS.node_of t' c == Some (CS.NodeArray ids (snd r)));
      assert (CS.interp_node t' c == ArraySort (L.map (CS.interp_node t') ids) (CS.interp_node t' (snd r)));
      assert (L.map (CS.interp_node t') ids == L.map fst ds);
      assert (CS.interp_node t' (snd r) == fst r);
      assert (csort_ok g' (ArraySort (L.map fst ds) (fst r), c))
    | _ -> ()

(* A variable of sort `c`. *)
let add_var (g:cgraph) (n:nat) (c:csort) : built =
  put_node g (T.ENVar n (snd c)) (Var n (fst c)) 0 g.prep g.store

let built_ok (g:cgraph) (e:expr) (r:built) : prop =
  match r with
  | Built g' x -> graph_inv g' /\ cgrows g g' /\ x < node_count g' /\ value_of g' x == Some e
  | _ -> True

let lemma_add_var (g:cgraph) (n:nat) (c:csort)
  : Lemma (requires graph_inv g /\ csort_ok g c) (ensures built_ok g (Var n (fst c)) (add_var g n c))
  = lemma_put_node g (T.ENVar n (snd c)) (Var n (fst c)) 0 g.prep g.store;
    match add_var g n c with
    | Built g' x -> lemma_csort_grows g g' c; reveal_exact g' x; lemma_put_inv g (T.ENVar n (snd c)) (Var n (fst c)) g' x
    | _ -> ()

(* A declaration whose domain and range are given by checked ids. *)
noeq
type cdecl = { decl: func_decl; dom: list nat; rng: nat }

let decl_ok (g:cgraph) (d:cdecl) : prop =
  CS.all_below d.dom (sort_count g) /\ L.map (interp g) d.dom == d.decl.domain /\
  d.rng < sort_count g /\ interp g d.rng == d.decl.range

let lemma_decl_grows (g g':cgraph) (d:cdecl)
  : Lemma (requires cgrows g g' /\ decl_ok g d) (ensures decl_ok g' d)
  = CS.lemma_map_agree g.terms.T.sorts g'.terms.T.sorts (sort_count g) d.dom;
    CS.lemma_interp_agree g.terms.T.sorts g'.terms.T.sorts (sort_count g) d.rng;
    T.lemma_all_below_widen d.dom (sort_count g) (sort_count g')

noeq
type declared =
  | Declared : graph:cgraph -> decl:cdecl -> declared
  | DeclExhausted : phase:T.phase -> declared
  | DeclInvalid

(* The declaration `name` (interpretation `tag`, parameters `params`) applied
   to the nodes `xs`: its domain is their sorts, its range `r`. *)
let new_decl (g:cgraph) (name:string) (tag:option decl_kind) (params:list int) (xs:list nat) (r:csort) : declared =
  match read_children g xs [] [] g.prep g.store with
  | ChildrenExhausted p -> DeclExhausted p
  | ChildrenInvalid -> DeclInvalid
  | ChildrenRead vs ss prep store ->
    Declared ({ g with prep = prep; store = store })
             { decl = { decl_name = name; domain = L.map get_sort vs; range = fst r; interp = tag; int_params = params };
               dom = ss; rng = snd r }

let lemma_budget (g:cgraph) (prep store:nat)
  : Lemma (requires graph_inv g)
          (ensures graph_inv ({ g with prep = prep; store = store }) /\ cgrows g ({ g with prep = prep; store = store }))
  = let g' = { g with prep = prep; store = store } in
    let aux (y:nat) : Lemma (requires y < node_count g') (ensures node_exact g' y)
      = lemma_node_exact_grows g g' y in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let lemma_new_decl (g:cgraph) (name:string) (tag:option decl_kind) (params:list int) (xs:list nat) (r:csort)
  : Lemma (requires graph_inv g /\ csort_ok g r)
          (ensures (match new_decl g name tag params xs r with
                    | Declared g' d -> graph_inv g' /\ cgrows g g' /\ decl_ok g' d /\ node_count g' == node_count g
                    | _ -> True))
  = lemma_read_children_ok g xs g.prep g.store;
    match read_children g xs [] [] g.prep g.store with
    | ChildrenRead vs ss prep store -> lemma_budget g prep store
    | _ -> ()

(* The application of `d` to the nodes `xs`. *)
let add_app (g:cgraph) (d:cdecl) (xs:list nat) : built =
  match read_children g xs [] [] g.prep g.store with
  | ChildrenExhausted p -> BuildExhausted p
  | ChildrenInvalid -> BuildInvalid
  | ChildrenRead vs ss prep store ->
    let n = L.length vs in
    if prep < n then BuildExhausted T.Preparation
    else put_node g (T.ENApp (CS.same_ids ss d.dom) xs d.rng) (App d.decl vs) n (prep - n) store

let lemma_add_app (g:cgraph) (d:cdecl) (xs:list nat)
  : Lemma (requires graph_inv g /\ decl_ok g d)
          (ensures (match add_app g d xs with
                    | Built g' x -> graph_inv g' /\ cgrows g g' /\ x < node_count g' /\
                                    (exists (args:list expr). values_of g xs == Some args /\ value_of g' x == Some (App d.decl args))
                    | _ -> True))
  = lemma_read_children_ok g xs g.prep g.store;
    match read_children g xs [] [] g.prep g.store with
    | ChildrenRead vs ss prep store ->
      let n = L.length vs in
      if prep < n then ()
      else begin
        let node = T.ENApp (CS.same_ids ss d.dom) xs d.rng in
        T.lemma_same_ids_sorts g.terms.T.sorts ss d.dom vs d.decl.domain;
        lemma_put_node g node (App d.decl vs) n (prep - n) store;
        match put_node g node (App d.decl vs) n (prep - n) store with
        | Built g' x ->
          lemma_decl_grows g g' d;
          lemma_values_of_grows g g' xs;
          T.lemma_all_below_widen xs (node_count g) x;
          CS.lemma_map_agree g.terms.T.sorts g'.terms.T.sorts (sort_count g) d.dom;
          reveal_exact g' x;
          lemma_put_inv g node (App d.decl vs) g' x
        | _ -> ()
      end
    | _ -> ()

(* The quantifier of kind `k` over the sorts `bs` with body node `y`; its
   sort is the quantifier's (`quant_sort`), interned. *)
let add_quant (g:cgraph) (k:quantifier_kind) (bs:list csort) (y:nat) : built =
  match read_children g [y] [] [] g.prep g.store with
  | ChildrenExhausted p -> BuildExhausted p
  | ChildrenInvalid -> BuildInvalid
  | ChildrenRead [b] [bi] prep store ->
    let bids = L.map snd bs in
    let m = L.length bids in
    let interned = if k = Lambda_k then T.intern_array g.terms.T.sorts bids m bi prep store
                   else T.intern_base g.terms.T.sorts "Bool" prep store in
    (match interned with
     | CS.InternExhausted p -> BuildExhausted (T.sort_phase p)
     | CS.Interned t c w s ->
       let q = quant_sort k (L.map fst bs) (get_sort b) in
       let g1 = with_sorts g t w s in
       put_node g1 (T.ENQuant (T.quant_ok k c bi c) bids y c) (Quantifier k (L.map fst bs) q b) 0 w s)
  | ChildrenRead _ _ _ _ -> BuildInvalid

let lemma_add_quant (g:cgraph) (k:quantifier_kind) (bs:list csort) (y:nat)
  : Lemma (requires graph_inv g /\ csorts_ok g bs)
          (ensures (match add_quant g k bs y with
                    | Built g' x -> graph_inv g' /\ cgrows g g' /\ x < node_count g' /\
                                    (exists (b:expr). value_of g y == Some b /\
                                      value_of g' x == Some (Quantifier k (L.map fst bs) (quant_sort k (L.map fst bs) (get_sort b)) b))
                    | _ -> True))
  = lemma_read_children_ok g [y] g.prep g.store;
    match read_children g [y] [] [] g.prep g.store with
    | ChildrenRead [b] [bi] prep store ->
      let bids = L.map snd bs in
      let m = L.length bids in
      let t = g.terms.T.sorts in
      lemma_csorts_ids g bs;
      (if k = Lambda_k then T.lemma_intern_array t bids m bi prep store
       else T.lemma_intern_base t "Bool" prep store);
      (match (if k = Lambda_k then T.intern_array t bids m bi prep store else T.intern_base t "Bool" prep store) with
       | CS.Interned t' c w s ->
         let q = quant_sort k (L.map fst bs) (get_sort b) in
         let g1 = with_sorts g t' w s in
         lemma_with_sorts g t' w s;
         CS.lemma_map_agree t t' (sort_count g) bids;
         CS.lemma_interp_agree t t' (sort_count g) bi;
         T.lemma_all_below_widen bids (sort_count g) (sort_count g1);
         T.lemma_quant_node t' k (L.map fst bs) b bids bi c;
         T.lemma_quant_ok t' k (L.map fst bs) q b bids c bi c;
         let node = T.ENQuant (T.quant_ok k c bi c) bids y c in
         let v = Quantifier k (L.map fst bs) q b in
         assert (values_of g [y] == Some [b]);
         assert (value_of g y == Some b);
         assert (add_quant g k bs y == put_node g1 node v 0 w s);
         lemma_put_node g1 node v 0 w s;
         (match put_node g1 node v 0 w s with
          | Built g' x ->
            reveal_exact g' x;
            assert (node_exact g' x);
            lemma_put_inv g1 node v g' x;
            lemma_cgrows_trans g g1 g';
            assert (cgrows g g' /\ value_of g' x == Some v)
          | _ -> ())
       | _ -> ())
    | _ -> ()
