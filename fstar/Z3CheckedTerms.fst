(*
   Z3CheckedTerms.fst

   Checked preparation of the AST terms a checker actually consumes. A sort
   is interned into a `Z3CheckedSorts` table and an expression into a
   document-local CHECKED SCOPE-SHAPE graph, bottom-up, within explicit
   Preparation and Storage budgets:

   * `intern_sort` returns a checked id whose interpretation is exactly the
     sort (`lemma_intern_sort`); its names are counted by the bounded
     `Z3CheckedSorts.checked_name_units` and compared completely;
   * `prepare_expr` returns a node that `represents` the expression
     (`lemma_prepare_expr`): its kind, de Bruijn index, the checked ids of
     its sort annotations, its children (earlier nodes), and the outcome of
     its scope-independent sort conditions (`sorts_match` of an application,
     the sort of a quantifier) computed by comparing checked ids, which is
     sort equality (`Z3CheckedSorts.lemma_id_equal`).

   A node keeps what the scope check reads, not the declaration or the
   names of its expression: node ids are not compared and stand for no
   expression equality; rules are checked on the original expressions.
   Every node is a fresh tree node (no sharing is found or assumed).

   Both walks keep their pending work on explicit worklists and are self
   tail calls (loops on the Cherry backend): they need no stack in the depth
   of a sort or an expression.

   Units, charged before the step they pay for. Preparation: one per step
   of either walk; one per name character (`Z3CheckedSorts`); the table
   costs of `Z3CheckedSorts.intern`; `table_units` per expression node
   stored and one per child compared. Storage, the cells allocated: one per
   pushed frame, two per list element accumulated (the cell and its
   reversal or copy), `1 + table_units` plus one per child per expression
   node, and the cells of `Z3CheckedSorts.intern`. The units are an
   abstract count, not a time or memory bound.
*)
module Z3CheckedTerms

open Z3AstTheory
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts

let max_expr_nodes : nat = 4294967296

type phase =
  | Preparation
  | Validation
  | Storage

let sort_phase (p:CS.budget_phase) : phase =
  match p with CS.Preparation -> Preparation | CS.Storage -> Storage

(* --- Sort equality is structural equality ------------------------------------------- *)

let rec lemma_sort_eq (s t:sort)
  : Lemma (ensures sort_eq s t == (s = t)) (decreases s)
  = match s, t with
    | ArraySort d1 r1, ArraySort d2 r2 -> lemma_sort_list_eq d1 d2; lemma_sort_eq r1 r2
    | _, _ -> ()

and lemma_sort_list_eq (l1 l2:list sort)
  : Lemma (ensures sort_list_eq l1 l2 == (l1 = l2)) (decreases l1)
  = match l1, l2 with
    | a :: l1', b :: l2' -> lemma_sort_eq a b; lemma_sort_list_eq l1' l2'
    | _, _ -> ()

(* --- Interning: work never grows ---------------------------------------------------------- *)

let rec lemma_find_node_le (n:CS.sort_node) (cost work:nat) (bucket:list (nat & CS.sort_node))
  : Lemma (ensures (match CS.find_node n cost work bucket with
                    | Some (_, w) -> w <= work
                    | None -> True))
          (decreases bucket)
  = match bucket with
    | [] -> ()
    | (c, m) :: rest -> if work >= cost && not (CS.same_node m n) then lemma_find_node_le n cost (work - cost) rest

let intern_node (t:CS.sort_table) (n:CS.sort_node) (key cost work store:nat)
  : r:CS.interned{CS.Interned? r ==> CS.Interned?.work r <= work /\ CS.Interned?.store r <= store} =
  (match CS.charge work CS.table_units with
   | Some w -> lemma_find_node_le n cost w (CS.bucket_of t key)
   | None -> ());
  CS.intern t n key cost work store

let intern_base (t:CS.sort_table) (name:string) (work store:nat)
  : r:CS.interned{CS.Interned? r ==> CS.Interned?.work r <= work /\ CS.Interned?.store r <= store} =
  match CS.checked_name_units name work with
  | None -> CS.InternExhausted CS.Preparation
  | Some len -> intern_node t (CS.NodeBase name) (len % CS.bucket_count) (1 + len) (work - len) store

let intern_array (t:CS.sort_table) (ds:list nat) (arity r work store:nat)
  : r:CS.interned{CS.Interned? r ==> CS.Interned?.work r <= work /\ CS.Interned?.store r <= store} =
  intern_node t (CS.NodeArray ds r) (CS.mix (CS.ids_key 1 ds) r) (2 + arity) work store

(* --- Interning a sort, bottom-up over a worklist -------------------------------------------- *)

(* An array whose domain is being interned (`acc` holds the ids of the
   finished domain sorts, last first) or whose range is. *)
type sort_frame =
  | InDomain : acc:list nat -> count:nat -> todo:list sort -> range:sort -> sort_frame
  | InRange : domain:list nat -> count:nat -> sort_frame

type sort_focus =
  | Down : sort -> sort_focus
  | Up : nat -> sort_focus

noeq
type sort_result =
  | SortInterned : table:CS.sort_table -> id:nat -> work:nat -> store:nat -> sort_result
  | SortExhausted : phase:phase -> sort_result

noeq
type sort_stepped =
  | SNext : table:CS.sort_table -> focus:sort_focus -> stack:list sort_frame -> work:nat -> store:nat -> sort_stepped
  | SDone : result:sort_result -> sort_stepped

let sort_up (t:CS.sort_table) (c:nat) (stack:list sort_frame) (w store:nat)
  : r:sort_stepped{(SNext? r ==> SNext?.work r <= w /\ SNext?.store r <= store) /\
                   (SDone? r /\ SortInterned? (SDone?.result r) ==>
                      SortInterned?.work (SDone?.result r) <= w /\ SortInterned?.store (SDone?.result r) <= store)} =
  match stack with
  | [] -> SDone (SortInterned t c w store)
  | InDomain acc n todo r :: rest ->
    if store < 2 then SDone (SortExhausted Storage)
    else
      (match todo with
       | [] -> SNext t (Down r) (InRange (L.rev (c :: acc)) (n + 1) :: rest) w (store - 2)
       | d :: todo' -> SNext t (Down d) (InDomain (c :: acc) (n + 1) todo' r :: rest) w (store - 2))
  | InRange dom n :: rest ->
    (match intern_array t dom n c w store with
     | CS.Interned t' c' w' s' -> SNext t' (Up c') rest w' s'
     | CS.InternExhausted p -> SDone (SortExhausted (sort_phase p)))

let sort_step (t:CS.sort_table) (focus:sort_focus) (stack:list sort_frame) (w store:nat)
  : r:sort_stepped{(SNext? r ==> SNext?.work r <= w /\ SNext?.store r <= store) /\
                   (SDone? r /\ SortInterned? (SDone?.result r) ==>
                      SortInterned?.work (SDone?.result r) <= w /\ SortInterned?.store (SDone?.result r) <= store)} =
  match focus with
  | Down (BaseSort name) ->
    (match intern_base t name w store with
     | CS.Interned t' c w' s' -> SNext t' (Up c) stack w' s'
     | CS.InternExhausted p -> SDone (SortExhausted (sort_phase p)))
  | Down (ArraySort ds r) ->
    if store = 0 then SDone (SortExhausted Storage)
    else
      (match ds with
       | [] -> SNext t (Down r) (InRange [] 0 :: stack) w (store - 1)
       | d :: rest -> SNext t (Down d) (InDomain [] 0 rest r :: stack) w (store - 1))
  | Up c -> sort_up t c stack w store

let rec intern_sort_loop (t:CS.sort_table) (focus:sort_focus) (stack:list sort_frame) (work store:nat)
  : Tot (r:sort_result{SortInterned? r ==> SortInterned?.work r <= work /\ SortInterned?.store r <= store})
        (decreases work) =
  if work = 0 then SortExhausted Preparation
  else
    match sort_step t focus stack (work - 1) store with
    | SNext t' focus' stack' w' s' -> intern_sort_loop t' focus' stack' w' s'
    | SDone r -> r

let intern_sort (t:CS.sort_table) (s:sort) (work store:nat)
  : r:sort_result{SortInterned? r ==> SortInterned?.work r <= work /\ SortInterned?.store r <= store} =
  intern_sort_loop t (Down s) [] work store

(* The sorts `ss` in order; two storage units per sort for the accumulated id
   and its reversal. *)
noeq
type sorts_result =
  | SortsInterned : table:CS.sort_table -> ids:list nat -> count:nat -> work:nat -> store:nat -> sorts_result
  | SortsExhausted : phase:phase -> sorts_result

let rec intern_sorts_loop (t:CS.sort_table) (ss:list sort) (acc:list nat) (n work store:nat)
  : Tot sorts_result (decreases ss) =
  match ss with
  | [] -> SortsInterned t (L.rev acc) n work store
  | s :: rest ->
    if store < 2 then SortsExhausted Storage
    else
      (match intern_sort t s work (store - 2) with
       | SortInterned t' c w' s' -> intern_sorts_loop t' rest (c :: acc) (n + 1) w' s'
       | SortExhausted p -> SortsExhausted p)

let rec lemma_intern_sorts_loop_le (t:CS.sort_table) (ss:list sort) (acc:list nat) (n work store:nat)
  : Lemma (ensures (match intern_sorts_loop t ss acc n work store with
                    | SortsInterned _ _ _ w s -> w <= work /\ s <= store
                    | SortsExhausted _ -> True))
          (decreases ss)
  = match ss with
    | [] -> ()
    | s :: rest ->
      if store < 2 then ()
      else
        (match intern_sort t s work (store - 2) with
         | SortInterned t' c w' s' -> lemma_intern_sorts_loop_le t' rest (c :: acc) (n + 1) w' s'
         | _ -> ())

let intern_sorts (t:CS.sort_table) (ss:list sort) (work store:nat)
  : r:sorts_result{SortsInterned? r ==> SortsInterned?.work r <= work /\ SortsInterned?.store r <= store} =
  lemma_intern_sorts_loop_le t ss [] 0 work store;
  intern_sorts_loop t ss [] 0 work store

(* --- What interning earns -------------------------------------------------------------------- *)

unfold noextract
let interp = CS.interp_node

let table_grows (t t':CS.sort_table) : prop =
  t.CS.node_count <= t'.CS.node_count /\ CS.agree_below t t' t.CS.node_count

noextract
let rec plug (t:CS.sort_table) (stack:list sort_frame) (s:sort) : Tot sort (decreases stack) =
  match stack with
  | [] -> s
  | InDomain acc _ todo r :: rest -> plug t rest (ArraySort (L.append (L.map (interp t) (L.rev acc)) (s :: todo)) r)
  | InRange dom _ :: rest -> plug t rest (ArraySort (L.map (interp t) dom) s)

noextract
let rec stack_below (stack:list sort_frame) (bound:nat) : Tot bool (decreases stack) =
  match stack with
  | [] -> true
  | InDomain acc _ _ _ :: rest -> CS.all_below acc bound && stack_below rest bound
  | InRange dom _ :: rest -> CS.all_below dom bound && stack_below rest bound

noextract
let focus_sort (t:CS.sort_table) (f:sort_focus) : sort =
  match f with Down s -> s | Up c -> interp t c

let focus_below (f:sort_focus) (bound:nat) : bool =
  match f with Down _ -> true | Up c -> c < bound

let rec lemma_all_below_widen (ds:list nat) (b b':nat)
  : Lemma (requires CS.all_below ds b /\ b <= b') (ensures CS.all_below ds b') (decreases ds)
  = match ds with [] -> () | _ :: rest -> lemma_all_below_widen rest b b'

let rec lemma_stack_below_widen (stack:list sort_frame) (b b':nat)
  : Lemma (requires stack_below stack b /\ b <= b') (ensures stack_below stack b') (decreases stack)
  = match stack with
    | [] -> ()
    | InDomain acc _ _ _ :: rest -> lemma_all_below_widen acc b b'; lemma_stack_below_widen rest b b'
    | InRange dom _ :: rest -> lemma_all_below_widen dom b b'; lemma_stack_below_widen rest b b'

let rec lemma_all_below_append (a b:list nat) (bound:nat)
  : Lemma (CS.all_below (L.append a b) bound == (CS.all_below a bound && CS.all_below b bound)) (decreases a)
  = match a with [] -> () | _ :: rest -> lemma_all_below_append rest b bound

let rec lemma_all_below_rev (ds:list nat) (bound:nat)
  : Lemma (CS.all_below (L.rev ds) bound == CS.all_below ds bound) (decreases ds)
  = match ds with
    | [] -> ()
    | d :: rest ->
      Z3List.lemma_rev_cons d rest;
      lemma_all_below_append (L.rev rest) [d] bound;
      lemma_all_below_rev rest bound

let rec lemma_plug_agree (t t':CS.sort_table) (stack:list sort_frame) (s:sort)
  : Lemma (requires table_grows t t' /\ stack_below stack t.CS.node_count)
          (ensures plug t' stack s == plug t stack s)
          (decreases stack)
  = match stack with
    | [] -> ()
    | InDomain acc _ todo r :: rest ->
      lemma_all_below_rev acc t.CS.node_count;
      CS.lemma_map_agree t t' t.CS.node_count (L.rev acc);
      lemma_plug_agree t t' rest (ArraySort (L.append (L.map (interp t) (L.rev acc)) (s :: todo)) r)
    | InRange dom _ :: rest ->
      CS.lemma_map_agree t t' t.CS.node_count dom;
      lemma_plug_agree t t' rest (ArraySort (L.map (interp t) dom) s)

let interned_into (t:CS.sort_table) (r:CS.interned) (n:CS.sort_node) : prop =
  match r with
  | CS.Interned t' c _ _ ->
    CS.valid_table t' /\ table_grows t t' /\ c < t'.CS.node_count /\ CS.node_of t' c == Some n
  | CS.InternExhausted _ -> True

let lemma_intern_base (t:CS.sort_table) (name:string) (work store:nat)
  : Lemma (requires CS.valid_table t)
          (ensures interned_into t (intern_base t name work store) (CS.NodeBase name))
  = match CS.checked_name_units name work with
    | None -> ()
    | Some len -> CS.lemma_intern t (CS.NodeBase name) (len % CS.bucket_count) (1 + len) (work - len) store

let lemma_intern_array (t:CS.sort_table) (ds:list nat) (arity r work store:nat)
  : Lemma (requires CS.valid_table t /\ CS.all_below ds t.CS.node_count /\ r < t.CS.node_count)
          (ensures interned_into t (intern_array t ds arity r work store) (CS.NodeArray ds r))
  = CS.lemma_intern t (CS.NodeArray ds r) (CS.mix (CS.ids_key 1 ds) r) (2 + arity) work store

let sort_loop_ok (t:CS.sort_table) (target:sort) (r:sort_result) : prop =
  match r with
  | SortInterned t' c _ _ -> CS.valid_table t' /\ table_grows t t' /\ c < t'.CS.node_count /\ interp t' c == target
  | SortExhausted _ -> True

let lemma_table_grows_trans (t1 t2 t3:CS.sort_table)
  : Lemma (requires table_grows t1 t2 /\ table_grows t2 t3) (ensures table_grows t1 t3)
  = ()

let lemma_sort_loop_trans (t t':CS.sort_table) (target:sort) (r:sort_result)
  : Lemma (requires table_grows t t' /\ sort_loop_ok t' target r) (ensures sort_loop_ok t target r)
  = match r with
    | SortInterned t'' _ _ _ -> lemma_table_grows_trans t t' t''
    | _ -> ()

let lemma_map_rev_cons (t:CS.sort_table) (c:nat) (acc:list nat)
  : Lemma (L.map (interp t) (L.rev (c :: acc)) == L.append (L.map (interp t) (L.rev acc)) [interp t c])
  = Z3List.lemma_rev_cons c acc;
    FStar.List.Tot.Properties.map_append (interp t) (L.rev acc) [c]

let sort_inv (t:CS.sort_table) (focus:sort_focus) (stack:list sort_frame) (target:sort) : prop =
  CS.valid_table t /\ focus_below focus t.CS.node_count /\ stack_below stack t.CS.node_count /\
  plug t stack (focus_sort t focus) == target

let sort_next_ok (t:CS.sort_table) (target:sort) (r:sort_stepped) : prop =
  match r with
  | SNext t' focus' stack' _ _ -> table_grows t t' /\ sort_inv t' focus' stack' target
  | SDone r -> sort_loop_ok t target r

let lemma_table_grows_refl (t:CS.sort_table) : Lemma (table_grows t t) = ()

let lemma_sort_step_base (t:CS.sort_table) (name:string) (stack:list sort_frame) (target:sort) (w store:nat)
  : Lemma (requires sort_inv t (Down (BaseSort name)) stack target)
          (ensures sort_next_ok t target (sort_step t (Down (BaseSort name)) stack w store))
  = lemma_intern_base t name w store;
    match intern_base t name w store with
    | CS.Interned t' c w' s' ->
      CS.lemma_interp_node t' c;
      lemma_plug_agree t t' stack (BaseSort name);
      lemma_stack_below_widen stack t.CS.node_count t'.CS.node_count
    | CS.InternExhausted _ -> ()

let lemma_sort_step_array (t:CS.sort_table) (ds:list sort) (r:sort) (stack:list sort_frame) (target:sort) (w store:nat)
  : Lemma (requires sort_inv t (Down (ArraySort ds r)) stack target)
          (ensures sort_next_ok t target (sort_step t (Down (ArraySort ds r)) stack w store))
  = lemma_table_grows_refl t

let lemma_sort_up_domain_last (t:CS.sort_table) (c:nat) (acc:list nat) (n:nat) (r:sort) (rest:list sort_frame)
                              (target:sort)
  : Lemma (requires sort_inv t (Up c) (InDomain acc n [] r :: rest) target)
          (ensures sort_inv t (Down r) (InRange (L.rev (c :: acc)) (n + 1) :: rest) target)
  = lemma_map_rev_cons t c acc;
    lemma_all_below_rev (c :: acc) t.CS.node_count

let lemma_sort_up_domain_next (t:CS.sort_table) (c:nat) (acc:list nat) (n:nat) (d:sort) (todo':list sort) (r:sort)
                              (rest:list sort_frame) (target:sort)
  : Lemma (requires sort_inv t (Up c) (InDomain acc n (d :: todo') r :: rest) target)
          (ensures sort_inv t (Down d) (InDomain (c :: acc) (n + 1) todo' r :: rest) target)
  = lemma_map_rev_cons t c acc;
    L.append_assoc (L.map (interp t) (L.rev acc)) [interp t c] (d :: todo')

let lemma_sort_up_range (t:CS.sort_table) (c:nat) (dom:list nat) (n:nat) (rest:list sort_frame) (target:sort) (w store:nat)
  : Lemma (requires sort_inv t (Up c) (InRange dom n :: rest) target)
          (ensures sort_next_ok t target (sort_up t c (InRange dom n :: rest) w store))
  = lemma_intern_array t dom n c w store;
    match intern_array t dom n c w store with
    | CS.Interned t' c' w' s' ->
      CS.lemma_interp_node t' c';
      CS.lemma_map_agree t t' t.CS.node_count dom;
      CS.lemma_interp_agree t t' t.CS.node_count c;
      lemma_plug_agree t t' rest (ArraySort (L.map (interp t) dom) (interp t c));
      lemma_stack_below_widen rest t.CS.node_count t'.CS.node_count
    | CS.InternExhausted _ -> ()

let lemma_sort_up (t:CS.sort_table) (c:nat) (stack:list sort_frame) (target:sort) (w store:nat)
  : Lemma (requires sort_inv t (Up c) stack target)
          (ensures sort_next_ok t target (sort_up t c stack w store))
  = lemma_table_grows_refl t;
    match stack with
    | [] -> ()
    | InDomain acc n todo r :: rest ->
      (match todo with
       | [] -> lemma_sort_up_domain_last t c acc n r rest target
       | d :: todo' -> lemma_sort_up_domain_next t c acc n d todo' r rest target)
    | InRange dom n :: rest -> lemma_sort_up_range t c dom n rest target w store

let lemma_sort_step (t:CS.sort_table) (focus:sort_focus) (stack:list sort_frame) (target:sort) (w store:nat)
  : Lemma (requires sort_inv t focus stack target)
          (ensures sort_next_ok t target (sort_step t focus stack w store))
  = match focus with
    | Down (BaseSort name) -> lemma_sort_step_base t name stack target w store
    | Down (ArraySort ds r) -> lemma_sort_step_array t ds r stack target w store
    | Up c -> lemma_sort_up t c stack target w store

let rec lemma_intern_sort_loop (t:CS.sort_table) (focus:sort_focus) (stack:list sort_frame)
                               (work store:nat) (target:sort)
  : Lemma (requires sort_inv t focus stack target)
          (ensures sort_loop_ok t target (intern_sort_loop t focus stack work store))
          (decreases work)
  = if work = 0 then ()
    else begin
      lemma_sort_step t focus stack target (work - 1) store;
      match sort_step t focus stack (work - 1) store with
      | SNext t' focus' stack' w' s' ->
        lemma_intern_sort_loop t' focus' stack' w' s' target;
        lemma_sort_loop_trans t t' target (intern_sort_loop t' focus' stack' w' s')
      | SDone _ -> ()
    end

let lemma_intern_sort (t:CS.sort_table) (s:sort) (work store:nat)
  : Lemma (requires CS.valid_table t) (ensures sort_loop_ok t s (intern_sort t s work store))
  = lemma_intern_sort_loop t (Down s) [] work store s

let sorts_ok (t:CS.sort_table) (ss:list sort) (r:sorts_result) : prop =
  match r with
  | SortsInterned t' ids n _ _ ->
    CS.valid_table t' /\ table_grows t t' /\ CS.all_below ids t'.CS.node_count /\
    L.map (interp t') ids == ss /\ n == L.length ss
  | SortsExhausted _ -> True

let rec lemma_intern_sorts_loop (t:CS.sort_table) (ss:list sort) (acc:list nat) (n work store:nat)
                                (prefix:list sort)
  : Lemma (requires CS.valid_table t /\ CS.all_below acc t.CS.node_count /\
                    L.map (interp t) (L.rev acc) == prefix /\ n == L.length prefix)
          (ensures sorts_ok t (L.append prefix ss) (intern_sorts_loop t ss acc n work store))
          (decreases ss)
  = match ss with
    | [] ->
      L.append_l_nil prefix;
      lemma_all_below_rev acc t.CS.node_count
    | s :: rest ->
      if store < 2 then ()
      else begin
        lemma_intern_sort t s work (store - 2);
        match intern_sort t s work (store - 2) with
        | SortInterned t' c w' s' ->
          lemma_all_below_rev acc t.CS.node_count;
          CS.lemma_map_agree t t' t.CS.node_count (L.rev acc);
          lemma_all_below_widen acc t.CS.node_count t'.CS.node_count;
          lemma_map_rev_cons t' c acc;
          FStar.List.Tot.Properties.append_length prefix [s];
          L.append_assoc prefix [s] rest;
          lemma_intern_sorts_loop t' rest (c :: acc) (n + 1) w' s' (L.append prefix [s]);
          (match intern_sorts_loop t' rest (c :: acc) (n + 1) w' s' with
           | SortsInterned t'' _ _ _ _ -> lemma_table_grows_trans t t' t''
           | _ -> ())
        | SortExhausted _ -> ()
      end

let lemma_intern_sorts (t:CS.sort_table) (ss:list sort) (work store:nat)
  : Lemma (requires CS.valid_table t) (ensures sorts_ok t ss (intern_sorts t ss work store))
  = lemma_intern_sorts_loop t ss [] 0 work store []

(* --- The expression graph --------------------------------------------------------------------- *)

type enode =
  | ENVar : index:nat -> sort:nat -> enode
  | ENApp : ok:bool -> args:list nat -> sort:nat -> enode
  | ENQuant : ok:bool -> binders:list nat -> body:nat -> sort:nat -> enode

noeq
type term_graph = {
  sorts: CS.sort_table;
  expr_nodes: I.index_tree enode;
  expr_count: nat;
}

let empty_graph : term_graph = { sorts = CS.empty_table; expr_nodes = I.Empty; expr_count = 0 }

let expr_node (g:term_graph) (x:nat) : option enode = I.index_get g.expr_nodes x

let graph_grows (g g':term_graph) : prop =
  table_grows g.sorts g'.sorts /\ g.expr_count <= g'.expr_count /\
  (forall (x:nat). x < g.expr_count ==> expr_node g' x == expr_node g x)

let sort_ok (g:term_graph) (i:nat) : bool = i < g.sorts.CS.node_count

(* `e` is node `x`: same kind and index, checked sort ids that denote its
   sort annotations, children that are earlier nodes denoting its
   subexpressions, and the results of its scope-independent conditions. *)
noextract
let rec represents (g:term_graph) (x:nat) (e:expr) : Tot prop (decreases e) =
  x < g.expr_count /\
  (match e, expr_node g x with
   | Var n s, Some (ENVar m i) -> m == n /\ sort_ok g i /\ interp g.sorts i == s
   | App f args, Some (ENApp ok xs i) ->
     sort_ok g i /\ interp g.sorts i == f.range /\ ok == sorts_match args f.domain /\
     CS.all_below xs x /\ represents_list g xs args
   | Quantifier k bs q b, Some (ENQuant ok ys y i) ->
     CS.all_below ys g.sorts.CS.node_count /\ L.map (interp g.sorts) ys == bs /\
     sort_ok g i /\ interp g.sorts i == q /\
     ok == (q = quant_sort k bs (get_sort b) && (k = Lambda_k || get_sort b = bool_sort)) /\
     y < x /\ represents g y b
   | _, _ -> False)

and represents_list (g:term_graph) (xs:list nat) (args:list expr) : Tot prop (decreases args) =
  match xs, args with
  | [], [] -> True
  | x :: xs', a :: args' -> represents g x a /\ represents_list g xs' args'
  | _, _ -> False

let rec lemma_represents_grows (g g':term_graph) (x:nat) (e:expr)
  : Lemma (requires graph_grows g g' /\ represents g x e) (ensures represents g' x e) (decreases e)
  = match e, expr_node g x with
    | Var _ _, Some (ENVar _ i) -> CS.lemma_interp_agree g.sorts g'.sorts g.sorts.CS.node_count i
    | App f args, Some (ENApp _ xs i) ->
      CS.lemma_interp_agree g.sorts g'.sorts g.sorts.CS.node_count i;
      lemma_represents_list_grows g g' xs args
    | Quantifier _ _ _ b, Some (ENQuant _ ys y i) ->
      CS.lemma_interp_agree g.sorts g'.sorts g.sorts.CS.node_count i;
      CS.lemma_map_agree g.sorts g'.sorts g.sorts.CS.node_count ys;
      lemma_all_below_widen ys g.sorts.CS.node_count g'.sorts.CS.node_count;
      lemma_represents_grows g g' y b
    | _, _ -> ()

and lemma_represents_list_grows (g g':term_graph) (xs:list nat) (args:list expr)
  : Lemma (requires graph_grows g g' /\ represents_list g xs args)
          (ensures represents_list g' xs args) (decreases args)
  = match xs, args with
    | x :: xs', a :: args' -> lemma_represents_grows g g' x a; lemma_represents_list_grows g g' xs' args'
    | _, _ -> ()

(* --- Preparing an expression, bottom-up over a worklist ---------------------------------------- *)

noeq
type added =
  | Added : graph:term_graph -> node:nat -> work:nat -> store:nat -> added
  | AddExhausted : phase:phase -> added

(* Store `n`, with `children` child ids, as the next node. *)
let add_node (g:term_graph) (n:enode) (children work store:nat)
  : r:added{Added? r ==> Added?.work r <= work /\ Added?.store r <= store} =
  if work < CS.table_units then AddExhausted Preparation
  else if store < 1 + CS.table_units + children || g.expr_count >= max_expr_nodes then AddExhausted Storage
  else Added ({ g with expr_nodes = I.index_put g.expr_nodes g.expr_count n; expr_count = g.expr_count + 1 })
             g.expr_count (work - CS.table_units) (store - (1 + CS.table_units + children))

(* A pending application (`acc` holds its finished children, last first:
   node, sort id and expression) or the body of a pending quantifier. *)
type expr_frame =
  | FApp : parent:expr -> domain:list nat -> range:nat -> acc:list (nat & nat & expr) -> count:nat ->
           todo:list expr -> expr_frame
  | FQuant : parent:expr -> binders:list nat -> count:nat -> sort:nat -> expr_frame

type expr_focus =
  | EDown : expr -> expr_focus
  | EUp : node:nat -> sort:nat -> e:expr -> expr_focus

noeq
type prepared =
  | Prepared : graph:term_graph -> node:nat -> sort:nat -> work:nat -> store:nat -> prepared
  | PrepExhausted : phase:phase -> prepared

(* The children of a finished application, in order: their nodes and sort ids. *)
let rec children (acc:list (nat & nat & expr)) (xs ss:list nat) : Tot (list nat & list nat) (decreases acc) =
  match acc with
  | [] -> (xs, ss)
  | (x, i, _) :: rest -> children rest (x :: xs) (i :: ss)

let finish_app (g:term_graph) (dom:list nat) (r:nat) (acc:list (nat & nat & expr)) (n work store:nat)
  : res:added{Added? res ==> Added?.work res <= work /\ Added?.store res <= store} =
  if work < n then AddExhausted Preparation
  else if store < 2 * n then AddExhausted Storage
  else
    let xs, ss = children acc [] [] in
    add_node g (ENApp (CS.same_ids ss dom) xs r) n (work - n) (store - 2 * n)

let quant_ok (k:quantifier_kind) (qi bi c:nat) : bool = if k = Lambda_k then qi = c else qi = c && bi = c

let finish_quant (g:term_graph) (k:quantifier_kind) (bids:list nat) (bn qi y bi work store:nat)
  : res:added{Added? res ==> Added?.work res <= work /\ Added?.store res <= store} =
  match (if k = Lambda_k then intern_array g.sorts bids bn bi work store
         else intern_base g.sorts "Bool" work store) with
  | CS.InternExhausted p -> AddExhausted (sort_phase p)
  | CS.Interned t c w s ->
    add_node ({ g with sorts = t }) (ENQuant (quant_ok k qi bi c) bids y qi) 0 w s

noeq
type stepped =
  | Next : graph:term_graph -> focus:expr_focus -> stack:list expr_frame -> work:nat -> store:nat -> stepped
  | Finished : result:prepared -> stepped

let down_var (g:term_graph) (n:nat) (s:sort) (e:expr) (stack:list expr_frame) (w store:nat)
  : r:stepped{Next? r ==> Next?.work r <= w} =
  match intern_sort g.sorts s w store with
  | SortExhausted p -> Finished (PrepExhausted p)
  | SortInterned t c w1 s1 ->
    (match add_node ({ g with sorts = t }) (ENVar n c) 0 w1 s1 with
     | Added g' x w2 s2 -> Next g' (EUp x c e) stack w2 s2
     | AddExhausted p -> Finished (PrepExhausted p))

let down_app (g:term_graph) (f:func_decl) (args:list expr) (e:expr) (stack:list expr_frame) (w store:nat)
  : r:stepped{Next? r ==> Next?.work r <= w} =
  match intern_sorts g.sorts f.domain w store with
  | SortsExhausted p -> Finished (PrepExhausted p)
  | SortsInterned t dom _ w1 s1 ->
    (match intern_sort t f.range w1 s1 with
     | SortExhausted p -> Finished (PrepExhausted p)
     | SortInterned t' r w2 s2 ->
       let g1 = { g with sorts = t' } in
       (match args with
        | [] ->
          (match finish_app g1 dom r [] 0 w2 s2 with
           | Added g' x w3 s3 -> Next g' (EUp x r e) stack w3 s3
           | AddExhausted p -> Finished (PrepExhausted p))
        | a :: rest ->
          if s2 = 0 then Finished (PrepExhausted Storage)
          else Next g1 (EDown a) (FApp e dom r [] 0 rest :: stack) w2 (s2 - 1)))

let down_quant (g:term_graph) (bs:list sort) (q:sort) (b:expr) (e:expr) (stack:list expr_frame) (w store:nat)
  : r:stepped{Next? r ==> Next?.work r <= w} =
  match intern_sorts g.sorts bs w store with
  | SortsExhausted p -> Finished (PrepExhausted p)
  | SortsInterned t bids bn w1 s1 ->
    (match intern_sort t q w1 s1 with
     | SortExhausted p -> Finished (PrepExhausted p)
     | SortInterned t' qi w2 s2 ->
       if s2 = 0 then Finished (PrepExhausted Storage)
       else Next ({ g with sorts = t' }) (EDown b) (FQuant e bids bn qi :: stack) w2 (s2 - 1))

let up_step (g:term_graph) (x i:nat) (e:expr) (stack:list expr_frame) (w store:nat)
  : r:stepped{Next? r ==> Next?.work r <= w} =
  match stack with
  | [] -> Finished (Prepared g x i w store)
  | FApp parent dom r acc n todo :: rest ->
    if store = 0 then Finished (PrepExhausted Storage)
    else
      (match todo with
       | a :: todo' -> Next g (EDown a) (FApp parent dom r ((x, i, e) :: acc) (n + 1) todo' :: rest) w (store - 1)
       | [] ->
         (match finish_app g dom r ((x, i, e) :: acc) (n + 1) w (store - 1) with
          | Added g' x' w' s' -> Next g' (EUp x' r parent) rest w' s'
          | AddExhausted p -> Finished (PrepExhausted p)))
  | FQuant parent bids bn qi :: rest ->
    (match parent with
     | Quantifier k _ _ _ ->
       (match finish_quant g k bids bn qi x i w store with
        | Added g' x' w' s' -> Next g' (EUp x' qi parent) rest w' s'
        | AddExhausted p -> Finished (PrepExhausted p))
     | _ -> Finished (PrepExhausted Preparation))

let prep_step (g:term_graph) (focus:expr_focus) (stack:list expr_frame) (w store:nat)
  : r:stepped{Next? r ==> Next?.work r <= w} =
  match focus with
  | EDown e ->
    (match e with
     | Var n s -> down_var g n s e stack w store
     | App f args -> down_app g f args e stack w store
     | Quantifier _ bs q b -> down_quant g bs q b e stack w store)
  | EUp x i e -> up_step g x i e stack w store

let rec prepare_loop (g:term_graph) (focus:expr_focus) (stack:list expr_frame) (work store:nat)
  : Tot prepared (decreases work) =
  if work = 0 then PrepExhausted Preparation
  else
    match prep_step g focus stack (work - 1) store with
    | Next g' focus' stack' w' s' -> prepare_loop g' focus' stack' w' s'
    | Finished r -> r

let prepare_expr (g:term_graph) (e:expr) (work store:nat) : prepared =
  prepare_loop g (EDown e) [] work store

(* --- What preparation earns ---------------------------------------------------------------------- *)

let graph_ok (g:term_graph) : prop = CS.valid_table g.sorts

(* The expressions of an application's finished children, in order, before `tail`. *)
noextract
let rec rev_exprs (acc:list (nat & nat & expr)) (tail:list expr) : Tot (list expr) (decreases acc) =
  match acc with
  | [] -> tail
  | (_, _, a) :: rest -> rev_exprs rest (a :: tail)

noextract
let rec acc_ok (g:term_graph) (bound:nat) (acc:list (nat & nat & expr)) : Tot prop (decreases acc) =
  match acc with
  | [] -> True
  | (x, i, a) :: rest ->
    x < bound /\ represents g x a /\ sort_ok g i /\ interp g.sorts i == get_sort a /\ acc_ok g bound rest

(* The stack's frames are the pending ancestors of `focus` within `target`. *)
noextract
let rec frames_ok (g:term_graph) (focus:expr) (stack:list expr_frame) (target:expr)
  : Tot prop (decreases stack) =
  match stack with
  | [] -> focus == target
  | FApp parent dom r acc _ todo :: rest ->
    (match parent with
     | App f args ->
       CS.all_below dom g.sorts.CS.node_count /\ L.map (interp g.sorts) dom == f.domain /\
       sort_ok g r /\ interp g.sorts r == f.range /\ acc_ok g g.expr_count acc /\
       args == rev_exprs acc (focus :: todo)
     | _ -> False) /\
    frames_ok g parent rest target
  | FQuant parent bids _ qi :: rest ->
    (match parent with
     | Quantifier k bs q b ->
       CS.all_below bids g.sorts.CS.node_count /\ L.map (interp g.sorts) bids == bs /\
       sort_ok g qi /\ interp g.sorts qi == q /\ focus == b
     | _ -> False) /\
    frames_ok g parent rest target

let rec lemma_acc_grows (g g':term_graph) (bound:nat) (acc:list (nat & nat & expr))
  : Lemma (requires graph_grows g g' /\ acc_ok g bound acc) (ensures acc_ok g' bound acc) (decreases acc)
  = match acc with
    | [] -> ()
    | (x, i, a) :: rest ->
      lemma_represents_grows g g' x a;
      CS.lemma_interp_agree g.sorts g'.sorts g.sorts.CS.node_count i;
      lemma_acc_grows g g' bound rest

let rec lemma_acc_widen (g:term_graph) (b b':nat) (acc:list (nat & nat & expr))
  : Lemma (requires acc_ok g b acc /\ b <= b') (ensures acc_ok g b' acc) (decreases acc)
  = match acc with [] -> () | _ :: rest -> lemma_acc_widen g b b' rest

let rec lemma_frames_grows (g g':term_graph) (focus:expr) (stack:list expr_frame) (target:expr)
  : Lemma (requires graph_grows g g' /\ frames_ok g focus stack target)
          (ensures frames_ok g' focus stack target) (decreases stack)
  = let n = g.sorts.CS.node_count in
    let n' = g'.sorts.CS.node_count in
    match stack with
    | [] -> ()
    | FApp parent dom r acc _ _ :: rest ->
      CS.lemma_map_agree g.sorts g'.sorts n dom;
      lemma_all_below_widen dom n n';
      CS.lemma_interp_agree g.sorts g'.sorts n r;
      lemma_acc_grows g g' g.expr_count acc;
      lemma_acc_widen g' g.expr_count g'.expr_count acc;
      lemma_frames_grows g g' parent rest target
    | FQuant parent bids _ qi :: rest ->
      CS.lemma_map_agree g.sorts g'.sorts n bids;
      lemma_all_below_widen bids n n';
      CS.lemma_interp_agree g.sorts g'.sorts n qi;
      lemma_frames_grows g g' parent rest target

let prep_ok (g:term_graph) (target:expr) (r:prepared) : prop =
  match r with
  | Prepared g' x i _ _ ->
    graph_ok g' /\ graph_grows g g' /\ represents g' x target /\ sort_ok g' i /\
    interp g'.sorts i == get_sort target
  | PrepExhausted _ -> True

let lemma_graph_grows_trans (g1 g2 g3:term_graph)
  : Lemma (requires graph_grows g1 g2 /\ graph_grows g2 g3) (ensures graph_grows g1 g3)
  = ()

let lemma_prep_trans (g g':term_graph) (target:expr) (r:prepared)
  : Lemma (requires graph_grows g g' /\ prep_ok g' target r) (ensures prep_ok g target r)
  = match r with
    | Prepared g'' _ _ _ _ -> lemma_graph_grows_trans g g' g''
    | _ -> ()

let lemma_add_node (g:term_graph) (n:enode) (children work store:nat)
  : Lemma (match add_node g n children work store with
           | Added g' x _ _ ->
             g'.sorts == g.sorts /\ graph_grows g g' /\ x == g.expr_count /\ g'.expr_count == x + 1 /\
             expr_node g' x == Some n
           | AddExhausted _ -> True)
  = match add_node g n children work store with
    | Added g' x _ _ ->
      let aux (y:nat) : Lemma (expr_node g' y == (if y = x then Some n else expr_node g y))
        = I.lemma_index_put g.expr_nodes x n y in
      FStar.Classical.forall_intro aux
    | _ -> ()

let lemma_sorts_graph (g:term_graph) (t:CS.sort_table)
  : Lemma (requires table_grows g.sorts t) (ensures graph_grows g ({ g with sorts = t }))
  = ()

(* The finished children: nodes denoting the arguments, and sort ids
   denoting their sorts. *)
let rec lemma_children (g:term_graph) (bound:nat) (acc:list (nat & nat & expr)) (xs ss:list nat) (tail:list expr)
  : Lemma (requires acc_ok g bound acc /\ represents_list g xs tail /\ CS.all_below xs bound /\
                    CS.all_below ss g.sorts.CS.node_count /\
                    L.map (interp g.sorts) ss == L.map get_sort tail)
          (ensures (let (xs', ss') = children acc xs ss in
                    represents_list g xs' (rev_exprs acc tail) /\ CS.all_below xs' bound /\
                    CS.all_below ss' g.sorts.CS.node_count /\
                    L.map (interp g.sorts) ss' == L.map get_sort (rev_exprs acc tail)))
          (decreases acc)
  = match acc with
    | [] -> ()
    | (x, i, a) :: rest -> lemma_children g bound rest (x :: xs) (i :: ss) (a :: tail)

let rec lemma_sorts_match_map (args:list expr) (dom:list sort)
  : Lemma (ensures sorts_match args dom == (L.map get_sort args = dom)) (decreases args)
  = match args, dom with
    | a :: args', d :: dom' -> lemma_sort_eq (get_sort a) d; lemma_sorts_match_map args' dom'
    | _, _ -> ()

let rec lemma_ids_injective (t:CS.sort_table) (a b:list nat)
  : Lemma (requires CS.valid_table t /\ CS.all_below a t.CS.node_count /\ CS.all_below b t.CS.node_count /\
                    L.map (interp t) a == L.map (interp t) b)
          (ensures a == b) (decreases a)
  = match a, b with
    | x :: a', y :: b' -> CS.lemma_interp_injective t x y; lemma_ids_injective t a' b'
    | _, _ -> ()

let lemma_same_ids_sorts (t:CS.sort_table) (ss dom:list nat) (args:list expr) (d:list sort)
  : Lemma (requires CS.valid_table t /\ CS.all_below ss t.CS.node_count /\ CS.all_below dom t.CS.node_count /\
                    L.map (interp t) ss == L.map get_sort args /\ L.map (interp t) dom == d)
          (ensures CS.same_ids ss dom == sorts_match args d)
  = CS.lemma_same_ids ss dom;
    lemma_sorts_match_map args d;
    FStar.Classical.move_requires (lemma_ids_injective t ss) dom

let lemma_finish_app (g:term_graph) (f:func_decl) (args:list expr) (dom:list nat) (r:nat)
                     (acc:list (nat & nat & expr)) (n work store:nat)
  : Lemma (requires graph_ok g /\ acc_ok g g.expr_count acc /\ args == rev_exprs acc [] /\
                    CS.all_below dom g.sorts.CS.node_count /\ L.map (interp g.sorts) dom == f.domain /\
                    sort_ok g r /\ interp g.sorts r == f.range)
          (ensures (match finish_app g dom r acc n work store with
                    | Added g' x _ _ -> graph_ok g' /\ graph_grows g g' /\ represents g' x (App f args)
                    | AddExhausted _ -> True))
  = if work < n || store < 2 * n then ()
    else begin
      let xs, ss = children acc [] [] in
      lemma_children g g.expr_count acc [] [] [];
      lemma_same_ids_sorts g.sorts ss dom args f.domain;
      let node = ENApp (CS.same_ids ss dom) xs r in
      lemma_add_node g node n (work - n) (store - 2 * n);
      match add_node g node n (work - n) (store - 2 * n) with
      | Added g' x _ _ -> lemma_represents_list_grows g g' xs args
      | _ -> ()
    end

(* The quantifier's sort conditions, decided by checked ids: `c` denotes the
   function-space sort of a lambda, or Bool. *)
let lemma_quant_ok (t:CS.sort_table) (k:quantifier_kind) (bs:list sort) (q:sort) (b:expr)
                   (bids:list nat) (qi bi c:nat)
  : Lemma (requires CS.valid_table t /\ CS.all_below bids t.CS.node_count /\ L.map (interp t) bids == bs /\
                    qi < t.CS.node_count /\ interp t qi == q /\ bi < t.CS.node_count /\ interp t bi == get_sort b /\
                    c < t.CS.node_count /\
                    interp t c == (if k = Lambda_k then ArraySort bs (get_sort b) else bool_sort))
          (ensures quant_ok k qi bi c == (q = quant_sort k bs (get_sort b) && (k = Lambda_k || get_sort b = bool_sort)))
  = CS.lemma_id_equal t qi c;
    CS.lemma_id_equal t bi c

let lemma_quant_node (t:CS.sort_table) (k:quantifier_kind) (bs:list sort) (b:expr) (bids:list nat) (bi c:nat)
  : Lemma (requires CS.valid_table t /\ c < t.CS.node_count /\ L.map (interp t) bids == bs /\ interp t bi == get_sort b /\
                    CS.node_of t c == Some (if k = Lambda_k then CS.NodeArray bids bi else CS.NodeBase "Bool"))
          (ensures interp t c == (if k = Lambda_k then ArraySort bs (get_sort b) else bool_sort))
  = CS.lemma_interp_node t c

let lemma_quant_added (g1:term_graph) (k:quantifier_kind) (bs:list sort) (q:sort) (b:expr)
                      (bids:list nat) (y qi:nat) (ok:bool) (w s:nat)
  : Lemma (requires graph_ok g1 /\ CS.all_below bids g1.sorts.CS.node_count /\ L.map (interp g1.sorts) bids == bs /\
                    sort_ok g1 qi /\ interp g1.sorts qi == q /\ represents g1 y b /\
                    ok == (q = quant_sort k bs (get_sort b) && (k = Lambda_k || get_sort b = bool_sort)))
          (ensures (match add_node g1 (ENQuant ok bids y qi) 0 w s with
                    | Added g' x _ _ -> graph_ok g' /\ graph_grows g1 g' /\ represents g' x (Quantifier k bs q b)
                    | AddExhausted _ -> True))
  = lemma_add_node g1 (ENQuant ok bids y qi) 0 w s;
    match add_node g1 (ENQuant ok bids y qi) 0 w s with
    | Added g' x _ _ -> lemma_represents_grows g1 g' y b
    | _ -> ()

(* The interned function-space or Bool sort, and the facts in the grown table. *)
let lemma_quant_interned (g:term_graph) (k:quantifier_kind) (bs:list sort) (q:sort) (b:expr)
                         (bids:list nat) (bn qi y bi work store:nat)
  : Lemma (requires graph_ok g /\ CS.all_below bids g.sorts.CS.node_count /\ L.map (interp g.sorts) bids == bs /\
                    sort_ok g qi /\ interp g.sorts qi == q /\ represents g y b /\ sort_ok g bi /\
                    interp g.sorts bi == get_sort b)
          (ensures (match (if k = Lambda_k then intern_array g.sorts bids bn bi work store
                           else intern_base g.sorts "Bool" work store) with
                    | CS.Interned t' c _ _ ->
                      let g1 = { g with sorts = t' } in
                      graph_ok g1 /\ graph_grows g g1 /\ CS.all_below bids t'.CS.node_count /\
                      L.map (interp t') bids == bs /\ sort_ok g1 qi /\ interp t' qi == q /\ represents g1 y b /\
                      quant_ok k qi bi c == (q = quant_sort k bs (get_sort b) && (k = Lambda_k || get_sort b = bool_sort))
                    | CS.InternExhausted _ -> True))
  = let t = g.sorts in
    let n = t.CS.node_count in
    (if k = Lambda_k then lemma_intern_array t bids bn bi work store
     else lemma_intern_base t "Bool" work store);
    match (if k = Lambda_k then intern_array t bids bn bi work store else intern_base t "Bool" work store) with
    | CS.InternExhausted _ -> ()
    | CS.Interned t' c w s ->
      CS.lemma_interp_agree t t' n qi;
      CS.lemma_interp_agree t t' n bi;
      CS.lemma_map_agree t t' n bids;
      lemma_all_below_widen bids n t'.CS.node_count;
      lemma_quant_node t' k bs b bids bi c;
      lemma_quant_ok t' k bs q b bids qi bi c;
      lemma_sorts_graph g t';
      lemma_represents_grows g ({ g with sorts = t' }) y b

let lemma_finish_quant (g:term_graph) (k:quantifier_kind) (bs:list sort) (q:sort) (b:expr)
                       (bids:list nat) (bn qi y bi work store:nat)
  : Lemma (requires graph_ok g /\ CS.all_below bids g.sorts.CS.node_count /\ L.map (interp g.sorts) bids == bs /\
                    sort_ok g qi /\ interp g.sorts qi == q /\ represents g y b /\ sort_ok g bi /\
                    interp g.sorts bi == get_sort b)
          (ensures (match finish_quant g k bids bn qi y bi work store with
                    | Added g' x _ _ -> graph_ok g' /\ graph_grows g g' /\ represents g' x (Quantifier k bs q b)
                    | AddExhausted _ -> True))
  = lemma_quant_interned g k bs q b bids bn qi y bi work store;
    match (if k = Lambda_k then intern_array g.sorts bids bn bi work store else intern_base g.sorts "Bool" work store) with
    | CS.InternExhausted _ -> ()
    | CS.Interned t' c w s ->
      let g1 = { g with sorts = t' } in
      lemma_quant_added g1 k bs q b bids y qi (quant_ok k qi bi c) w s;
      match add_node g1 (ENQuant (quant_ok k qi bi c) bids y qi) 0 w s with
      | Added g' _ _ _ -> lemma_graph_grows_trans g g1 g'
      | _ -> ()

let focus_ok (g:term_graph) (focus:expr_focus) (stack:list expr_frame) (target:expr) : prop =
  graph_ok g /\
  (match focus with
   | EDown e -> frames_ok g e stack target
   | EUp x i e -> represents g x e /\ sort_ok g i /\ interp g.sorts i == get_sort e /\ frames_ok g e stack target)

let lemma_down_var (g:term_graph) (n:nat) (s:sort) (stack:list expr_frame) (target:expr) (w store:nat)
  : Lemma (requires graph_ok g /\ frames_ok g (Var n s) stack target)
          (ensures (match intern_sort g.sorts s w store with
                    | SortExhausted _ -> True
                    | SortInterned t c w1 s1 ->
                      (match add_node ({ g with sorts = t }) (ENVar n c) 0 w1 s1 with
                       | Added g' x _ _ -> graph_grows g g' /\ focus_ok g' (EUp x c (Var n s)) stack target
                       | AddExhausted _ -> True)))
  = lemma_intern_sort g.sorts s w store;
    match intern_sort g.sorts s w store with
    | SortInterned t c w1 s1 ->
      let g1 = { g with sorts = t } in
      lemma_sorts_graph g t;
      lemma_add_node g1 (ENVar n c) 0 w1 s1;
      (match add_node g1 (ENVar n c) 0 w1 s1 with
       | Added g' x _ _ ->
         lemma_graph_grows_trans g g1 g';
         lemma_frames_grows g g' (Var n s) stack target
       | _ -> ())
    | _ -> ()

(* The declaration's domain and range, interned for an application. *)
let lemma_down_app_sorts (g:term_graph) (f:func_decl) (w store:nat)
  : Lemma (requires graph_ok g)
          (ensures (match intern_sorts g.sorts f.domain w store with
                    | SortsExhausted _ -> True
                    | SortsInterned t dom _ w1 s1 ->
                      (match intern_sort t f.range w1 s1 with
                       | SortExhausted _ -> True
                       | SortInterned t' r _ _ ->
                         let g1 = { g with sorts = t' } in
                         graph_ok g1 /\ graph_grows g g1 /\ CS.all_below dom t'.CS.node_count /\
                         L.map (interp t') dom == f.domain /\ sort_ok g1 r /\ interp t' r == f.range)))
  = lemma_intern_sorts g.sorts f.domain w store;
    match intern_sorts g.sorts f.domain w store with
    | SortsInterned t dom _ w1 s1 ->
      lemma_intern_sort t f.range w1 s1;
      (match intern_sort t f.range w1 s1 with
       | SortInterned t' r _ _ ->
         CS.lemma_map_agree t t' t.CS.node_count dom;
         lemma_all_below_widen dom t.CS.node_count t'.CS.node_count;
         lemma_table_grows_trans g.sorts t t'
       | _ -> ())
    | _ -> ()

let lemma_down_quant_sorts (g:term_graph) (bs:list sort) (q:sort) (w store:nat)
  : Lemma (requires graph_ok g)
          (ensures (match intern_sorts g.sorts bs w store with
                    | SortsExhausted _ -> True
                    | SortsInterned t bids _ w1 s1 ->
                      (match intern_sort t q w1 s1 with
                       | SortExhausted _ -> True
                       | SortInterned t' qi _ _ ->
                         let g1 = { g with sorts = t' } in
                         graph_ok g1 /\ graph_grows g g1 /\ CS.all_below bids t'.CS.node_count /\
                         L.map (interp t') bids == bs /\ sort_ok g1 qi /\ interp t' qi == q)))
  = lemma_intern_sorts g.sorts bs w store;
    match intern_sorts g.sorts bs w store with
    | SortsInterned t bids _ w1 s1 ->
      lemma_intern_sort t q w1 s1;
      (match intern_sort t q w1 s1 with
       | SortInterned t' qi _ _ ->
         CS.lemma_map_agree t t' t.CS.node_count bids;
         lemma_all_below_widen bids t.CS.node_count t'.CS.node_count;
         lemma_table_grows_trans g.sorts t t'
       | _ -> ())
    | _ -> ()

let lemma_up_app (g:term_graph) (x i:nat) (e:expr) (parent:expr) (dom:list nat) (r:nat)
                 (acc:list (nat & nat & expr)) (n:nat) (rest:list expr_frame) (target:expr) (w store:nat)
  : Lemma (requires focus_ok g (EUp x i e) (FApp parent dom r acc n [] :: rest) target)
          (ensures (match finish_app g dom r ((x, i, e) :: acc) (n + 1) w store with
                    | Added g' x' _ _ -> graph_grows g g' /\ focus_ok g' (EUp x' r parent) rest target
                    | AddExhausted _ -> True))
  = match parent with
    | App f args ->
      lemma_finish_app g f args dom r ((x, i, e) :: acc) (n + 1) w store;
      (match finish_app g dom r ((x, i, e) :: acc) (n + 1) w store with
       | Added g' _ _ _ ->
         CS.lemma_interp_agree g.sorts g'.sorts g.sorts.CS.node_count r;
         lemma_frames_grows g g' parent rest target
       | _ -> ())

let frame_parent (fr:expr_frame) : expr =
  match fr with FApp p _ _ _ _ _ -> p | FQuant p _ _ _ -> p

let lemma_frames_tail (g:term_graph) (focus:expr) (fr:expr_frame) (rest:list expr_frame) (target:expr)
  : Lemma (requires frames_ok g focus (fr :: rest) target) (ensures frames_ok g (frame_parent fr) rest target)
  = ()

let lemma_up_quant (g:term_graph) (x i:nat) (e:expr) (parent:expr) (bids:list nat) (bn qi:nat)
                   (rest:list expr_frame) (target:expr) (w store:nat)
  : Lemma (requires focus_ok g (EUp x i e) (FQuant parent bids bn qi :: rest) target /\ Quantifier? parent)
          (ensures (match finish_quant g (Quantifier?.qk parent) bids bn qi x i w store with
                    | Added g' x' _ _ -> graph_grows g g' /\ focus_ok g' (EUp x' qi parent) rest target
                    | AddExhausted _ -> True))
  = lemma_frames_tail g e (FQuant parent bids bn qi) rest target;
    match parent with
    | Quantifier k bs q b ->
      lemma_finish_quant g k bs q b bids bn qi x i w store;
      (match finish_quant g k bids bn qi x i w store with
       | Added g' _ _ _ ->
         CS.lemma_interp_agree g.sorts g'.sorts g.sorts.CS.node_count qi;
         lemma_frames_grows g g' parent rest target
       | _ -> ())

let lemma_graph_grows_refl (g:term_graph) : Lemma (graph_grows g g) = ()

let next_ok (g:term_graph) (target:expr) (r:stepped) : prop =
  match r with
  | Next g' focus' stack' _ _ -> graph_grows g g' /\ focus_ok g' focus' stack' target
  | Finished p -> prep_ok g target p

let lemma_down_var_step (g:term_graph) (n:nat) (s:sort) (e:expr) (stack:list expr_frame) (target:expr) (w store:nat)
  : Lemma (requires graph_ok g /\ e == Var n s /\ frames_ok g e stack target)
          (ensures next_ok g target (down_var g n s e stack w store))
  = lemma_down_var g n s stack target w store

let lemma_down_app_step (g:term_graph) (f:func_decl) (args:list expr) (e:expr) (stack:list expr_frame) (target:expr)
                        (w store:nat)
  : Lemma (requires graph_ok g /\ e == App f args /\ frames_ok g e stack target)
          (ensures next_ok g target (down_app g f args e stack w store))
  = lemma_down_app_sorts g f w store;
    match intern_sorts g.sorts f.domain w store with
    | SortsInterned t dom _ w1 s1 ->
      (match intern_sort t f.range w1 s1 with
       | SortInterned t' r w2 s2 ->
         let g1 = { g with sorts = t' } in
         lemma_frames_grows g g1 e stack target;
         (match args with
          | [] ->
            lemma_finish_app g1 f args dom r [] 0 w2 s2;
            (match finish_app g1 dom r [] 0 w2 s2 with
             | Added g' x w3 s3 ->
               CS.lemma_interp_agree g1.sorts g'.sorts g1.sorts.CS.node_count r;
               lemma_frames_grows g1 g' e stack target;
               lemma_graph_grows_trans g g1 g'
             | _ -> ())
          | _ -> ())
       | _ -> ())
    | _ -> ()

let lemma_down_quant_step (g:term_graph) (k:quantifier_kind) (bs:list sort) (q:sort) (b:expr) (e:expr)
                          (stack:list expr_frame) (target:expr) (w store:nat)
  : Lemma (requires graph_ok g /\ e == Quantifier k bs q b /\ frames_ok g e stack target)
          (ensures next_ok g target (down_quant g bs q b e stack w store))
  = lemma_down_quant_sorts g bs q w store;
    match intern_sorts g.sorts bs w store with
    | SortsInterned t bids bn w1 s1 ->
      (match intern_sort t q w1 s1 with
       | SortInterned t' qi w2 s2 -> lemma_frames_grows g ({ g with sorts = t' }) e stack target
       | _ -> ())
    | _ -> ()

let lemma_up_app_more (g:term_graph) (x i:nat) (e:expr) (parent:expr) (dom:list nat) (r:nat)
                      (acc:list (nat & nat & expr)) (n:nat) (a:expr) (todo':list expr) (rest:list expr_frame)
                      (target:expr)
  : Lemma (requires focus_ok g (EUp x i e) (FApp parent dom r acc n (a :: todo') :: rest) target)
          (ensures focus_ok g (EDown a) (FApp parent dom r ((x, i, e) :: acc) (n + 1) todo' :: rest) target)
  = ()

let lemma_up_step_app_more (g:term_graph) (x i:nat) (e:expr) (parent:expr) (dom:list nat) (r:nat)
                           (acc:list (nat & nat & expr)) (n:nat) (a:expr) (todo':list expr) (rest:list expr_frame)
                           (target:expr) (w s':nat)
  : Lemma (requires focus_ok g (EUp x i e) (FApp parent dom r acc n (a :: todo') :: rest) target)
          (ensures next_ok g target (up_step g x i e (FApp parent dom r acc n (a :: todo') :: rest) w (s' + 1)))
  = lemma_graph_grows_refl g;
    lemma_up_app_more g x i e parent dom r acc n a todo' rest target

let lemma_up_step_app_last (g:term_graph) (x i:nat) (e:expr) (parent:expr) (dom:list nat) (r:nat)
                           (acc:list (nat & nat & expr)) (n:nat) (rest:list expr_frame) (target:expr) (w s':nat)
  : Lemma (requires focus_ok g (EUp x i e) (FApp parent dom r acc n [] :: rest) target)
          (ensures next_ok g target (up_step g x i e (FApp parent dom r acc n [] :: rest) w (s' + 1)))
  = lemma_up_app g x i e parent dom r acc n rest target w s'

let lemma_up_step_app (g:term_graph) (x i:nat) (e:expr) (parent:expr) (dom:list nat) (r:nat)
                      (acc:list (nat & nat & expr)) (n:nat) (todo:list expr) (rest:list expr_frame)
                      (target:expr) (w store:nat)
  : Lemma (focus_ok g (EUp x i e) (FApp parent dom r acc n todo :: rest) target ==>
           next_ok g target (up_step g x i e (FApp parent dom r acc n todo :: rest) w store))
  = if store = 0 then ()
    else
      match todo with
      | a :: todo' ->
        FStar.Classical.move_requires (lemma_up_step_app_more g x i e parent dom r acc n a todo' rest target w) (store - 1)
      | [] ->
        FStar.Classical.move_requires (lemma_up_step_app_last g x i e parent dom r acc n rest target w) (store - 1)

let lemma_up_step_quant (g:term_graph) (x i:nat) (e:expr) (parent:expr) (bids:list nat) (bn qi:nat)
                        (rest:list expr_frame) (target:expr) (w store:nat)
  : Lemma (requires focus_ok g (EUp x i e) (FQuant parent bids bn qi :: rest) target)
          (ensures next_ok g target (up_step g x i e (FQuant parent bids bn qi :: rest) w store))
  = match parent with
    | Quantifier _ _ _ _ -> lemma_up_quant g x i e parent bids bn qi rest target w store
    | _ -> ()

let lemma_up_step (g:term_graph) (x i:nat) (e:expr) (stack:list expr_frame) (target:expr) (w store:nat)
  : Lemma (requires focus_ok g (EUp x i e) stack target)
          (ensures next_ok g target (up_step g x i e stack w store))
  = match stack with
    | [] -> lemma_graph_grows_refl g
    | FApp parent dom r acc n todo :: rest -> lemma_up_step_app g x i e parent dom r acc n todo rest target w store
    | FQuant parent bids bn qi :: rest -> lemma_up_step_quant g x i e parent bids bn qi rest target w store

let lemma_prep_step (g:term_graph) (focus:expr_focus) (stack:list expr_frame) (target:expr) (w store:nat)
  : Lemma (requires focus_ok g focus stack target)
          (ensures next_ok g target (prep_step g focus stack w store))
  = match focus with
    | EDown e ->
      (match e with
       | Var n s -> lemma_down_var_step g n s e stack target w store
       | App f args -> lemma_down_app_step g f args e stack target w store
       | Quantifier k bs q b -> lemma_down_quant_step g k bs q b e stack target w store)
    | EUp x i e -> lemma_up_step g x i e stack target w store

let rec lemma_prepare_loop (g:term_graph) (focus:expr_focus) (stack:list expr_frame) (work store:nat)
                           (target:expr)
  : Lemma (requires focus_ok g focus stack target)
          (ensures prep_ok g target (prepare_loop g focus stack work store))
          (decreases work)
  = if work = 0 then ()
    else begin
      lemma_prep_step g focus stack target (work - 1) store;
      match prep_step g focus stack (work - 1) store with
      | Next g' focus' stack' w' s' ->
        lemma_prepare_loop g' focus' stack' w' s' target;
        lemma_prep_trans g g' target (prepare_loop g' focus' stack' w' s')
      | Finished _ -> ()
    end

let lemma_prepare_expr (g:term_graph) (e:expr) (work store:nat)
  : Lemma (requires graph_ok g) (ensures prep_ok g e (prepare_expr g e work store))
  = lemma_prepare_loop g (EDown e) [] work store e
