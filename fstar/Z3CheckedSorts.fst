(*
   Z3CheckedSorts.fst

   Checked sort identities. `validate_sort_graph` reads an untrusted reflected
   sort graph (entries keyed by untrusted native ids, arrays referring to
   earlier entries by id) within explicit budgets and builds a document-local
   table in which every sort is stored once. Its success earns:

   * `lemma_validated`: every raw entry's id resolves to a checked id whose
     `interpret_sort` is exactly the entry's content (the complete name; the
     declared arity, the ordered domain and the range, through the ids they
     refer to);
   * `lemma_id_equal`: two checked ids are equal exactly when the sorts they
     denote are equal (canonical interning: `distinct_nodes` plus children
     that are earlier ids).

   Untrusted ids and buckets only locate candidates: a name is compared with
   complete string equality, an array by its ordered checked children. Every
   reference must name an earlier entry (so there are no cycles); a repeated
   id must denote the same sort; ids are in [0, 2^32).

   Names are counted by the caller's `name_counter`, given the remaining
   preparation budget: it returns the character count (`FStar.String.strlen`)
   when that is within the budget, else `None`, which is exhaustion. This
   module decodes no string. The contract states the result only; a counter
   that scans at most the budget plus one character is a runtime obligation
   (no such primitive exists on either backend yet). A name's bucket is its
   character count, so names of equal length share a bucket and are told
   apart by charged comparisons; an array's bucket mixes its checked children.

   Units, charged before the step they pay for. Preparation: one per entry,
   one per name character, `1 + table_units` per array reference,
   `table_units` per table lookup or update, and per bucket candidate compared
   `1 + characters` (names) or `2 + arity` (arrays). Storage, the cells this
   module allocates: one per entry (its state), two per array reference (the
   accumulated list and its reversal), `2 + 2 table_units` per new node (the
   node, its bucket cell and two copied tree paths) and `table_units` per new
   id binding (a copied path). `table_units` bounds the depth of a
   `Z3ProofIndex.index_tree` path for keys below 2^32 (ids, at most
   `max_sort_nodes` nodes) and 2^16 (buckets). The units are an abstract
   count, not a time or memory bound.
*)
module Z3CheckedSorts

open Z3AstTheory
module I = Z3ProofIndex
module L = FStar.List.Tot

let untrusted_id_limit : nat = 4294967296

let max_sort_nodes : nat = 4294967296

let bucket_count : nat = 65536

let table_units : nat = 33

type raw_sort =
  | RawBase : id:int -> name:string -> raw_sort
  | RawArray : id:int -> arity:int -> domain:list int -> range:int -> raw_sort

let raw_id (e:raw_sort) : int =
  match e with RawBase x _ -> x | RawArray x _ _ _ -> x

type sort_budget = { preparation: nat; storage: nat }

type budget_phase =
  | Preparation
  | Storage

type sort_graph_error =
  | MalformedId : id:int -> sort_graph_error
  | DanglingReference : id:int -> sort_graph_error
  | ConflictingDefinition : id:int -> sort_graph_error
  | WrongArity : id:int -> sort_graph_error

type sort_node =
  | NodeBase : name:string -> sort_node
  | NodeArray : domain:list nat -> range:nat -> sort_node

noeq
type sort_table = {
  nodes: I.index_tree sort_node;
  node_count: nat;
  buckets: I.index_tree (list (nat & sort_node));
}

(* --- Buckets: a hint, never an equality ------------------------------------------- *)

(* Exactly the character count when it is at most `limit`, else `None`. *)
type name_counter =
  s:string -> limit:nat ->
  r:option nat{r == (if FStar.String.strlen s <= limit then Some (FStar.String.strlen s) else None)}

let mix (h code:nat) : nat = (h * 31 + code) % bucket_count

let rec ids_key (h:nat) (ids:list nat) : Tot nat (decreases ids) =
  match ids with
  | [] -> h
  | i :: rest -> ids_key (mix h i) rest

noextract
let node_key (n:sort_node) : nat =
  match n with
  | NodeBase name -> FStar.String.strlen name % bucket_count
  | NodeArray ds r -> mix (ids_key 1 ds) r

(* --- The table and its meaning ------------------------------------------------------ *)

let node_of (t:sort_table) (i:nat) : option sort_node = I.index_get t.nodes i

let bucket_of (t:sort_table) (k:nat) : list (nat & sort_node) =
  match I.index_get t.buckets k with Some b -> b | None -> []

noextract
let rec interp_node (t:sort_table) (i:nat) : Tot sort (decreases %[i; 1; 0]) =
  match node_of t i with
  | Some (NodeArray ds r) -> ArraySort (interp_children t i ds) (if r < i then interp_node t r else BaseSort "")
  | Some (NodeBase name) -> BaseSort name
  | None -> BaseSort ""

and interp_children (t:sort_table) (i:nat) (ds:list nat) : Tot (list sort) (decreases %[i; 0; ds]) =
  match ds with
  | [] -> []
  | d :: rest -> (if d < i then interp_node t d else BaseSort "") :: interp_children t i rest

noextract
let rec all_below (ds:list nat) (bound:nat) : Tot bool (decreases ds) =
  match ds with
  | [] -> true
  | d :: rest -> d < bound && all_below rest bound

noextract
let children_below (n:sort_node) (bound:nat) : bool =
  match n with
  | NodeBase _ -> true
  | NodeArray ds r -> r < bound && all_below ds bound

let well_founded (t:sort_table) : prop =
  forall (i:nat). i < t.node_count ==> Some? (node_of t i) /\ children_below (Some?.v (node_of t i)) i

let distinct_nodes (t:sort_table) : prop =
  forall (i j:nat). i < t.node_count /\ j < t.node_count /\ node_of t i == node_of t j ==> i == j

let complete_buckets (t:sort_table) : prop =
  forall (i:nat). i < t.node_count /\ Some? (node_of t i) ==>
    L.mem (i, Some?.v (node_of t i)) (bucket_of t (node_key (Some?.v (node_of t i))))

let sound_buckets (t:sort_table) : prop =
  forall (k c:nat) (n:sort_node). L.mem (c, n) (bucket_of t k) ==> c < t.node_count /\ node_of t c == Some n

let valid_table (t:sort_table) : prop =
  well_founded t /\ distinct_nodes t /\ complete_buckets t /\ sound_buckets t

type checked_sort_graph = t:sort_table{valid_table t}

type sort_id (g:checked_sort_graph) = i:nat{i < g.node_count}

noextract
let interpret_sort (g:checked_sort_graph) (i:sort_id g) : sort = interp_node g i

let id_equal (g:checked_sort_graph) (i j:sort_id g) : bool = i = j

(* --- Equality of checked ids is equality of sorts ------------------------------------ *)

let rec lemma_interp_injective (t:sort_table{valid_table t}) (i j:nat)
  : Lemma (requires i < t.node_count /\ j < t.node_count /\ interp_node t i == interp_node t j)
          (ensures i == j)
          (decreases %[i + j; 1; 0])
  = match node_of t i, node_of t j with
    | Some (NodeArray ds r), Some (NodeArray es q) ->
      lemma_children_injective t i j ds es;
      lemma_interp_injective t r q
    | _, _ -> ()

and lemma_children_injective (t:sort_table{valid_table t}) (i j:nat) (ds es:list nat)
  : Lemma (requires i < t.node_count /\ j < t.node_count /\ all_below ds i /\ all_below es j /\
                    interp_children t i ds == interp_children t j es)
          (ensures ds == es)
          (decreases %[i + j; 0; ds])
  = match ds, es with
    | d :: ds', e :: es' ->
      lemma_interp_injective t d e;
      lemma_children_injective t i j ds' es'
    | _, _ -> ()

let lemma_id_equal (g:checked_sort_graph) (i j:sort_id g)
  : Lemma (id_equal g i j <==> interpret_sort g i == interpret_sort g j)
  = FStar.Classical.move_requires (lemma_interp_injective g i) j

let rec lemma_children_map (t:sort_table) (i:nat) (ds:list nat)
  : Lemma (requires all_below ds i) (ensures interp_children t i ds == L.map (interp_node t) ds) (decreases ds)
  = match ds with [] -> () | _ :: rest -> lemma_children_map t i rest

let lemma_interp_node (t:sort_table{valid_table t}) (c:nat{c < t.node_count})
  : Lemma (match node_of t c with
           | Some (NodeBase name) -> interp_node t c == BaseSort name
           | Some (NodeArray ds r) -> interp_node t c == ArraySort (L.map (interp_node t) ds) (interp_node t r)
           | None -> False)
  = match node_of t c with
    | Some (NodeArray ds r) -> lemma_children_map t c ds
    | _ -> ()

(* --- Extensions keep the meaning of earlier ids --------------------------------------- *)

let agree_below (t t':sort_table) (bound:nat) : prop =
  forall (j:nat). j < bound ==> node_of t' j == node_of t j

let rec lemma_interp_agree (t t':sort_table) (bound i:nat)
  : Lemma (requires agree_below t t' bound /\ i < bound)
          (ensures interp_node t' i == interp_node t i)
          (decreases %[i; 1; 0])
  = match node_of t i with
    | Some (NodeArray ds r) ->
      lemma_children_agree t t' bound i ds;
      if r < i then lemma_interp_agree t t' bound r
    | _ -> ()

and lemma_children_agree (t t':sort_table) (bound i:nat) (ds:list nat)
  : Lemma (requires agree_below t t' bound /\ i < bound)
          (ensures interp_children t' i ds == interp_children t i ds)
          (decreases %[i; 0; ds])
  = match ds with
    | [] -> ()
    | d :: rest ->
      (if d < i then lemma_interp_agree t t' bound d);
      lemma_children_agree t t' bound i rest

let rec lemma_map_agree (t t':sort_table) (bound:nat) (cs:list nat)
  : Lemma (requires agree_below t t' bound /\ all_below cs bound)
          (ensures L.map (interp_node t') cs == L.map (interp_node t) cs)
          (decreases cs)
  = match cs with
    | [] -> ()
    | c :: rest -> lemma_interp_agree t t' bound c; lemma_map_agree t t' bound rest

(* --- Interning one node ----------------------------------------------------------------- *)

let lemma_get_put (#a:Type) (tree:I.index_tree a) (key:nat) (value:a) (query:nat)
  : Lemma (I.index_get (I.index_put tree key value) query ==
           (if query = key then Some value else I.index_get tree query))
          [SMTPat (I.index_get (I.index_put tree key value) query)]
  = I.lemma_index_put tree key value query

let charge (work cost:nat) : option nat = if cost <= work then Some (work - cost) else None

let rec same_ids (a b:list nat) : Tot bool (decreases a) =
  match a, b with
  | [], [] -> true
  | x :: a', y :: b' -> if x = y then same_ids a' b' else false
  | _, _ -> false

let rec lemma_same_ids (a b:list nat) : Lemma (same_ids a b <==> a == b) (decreases a) =
  match a, b with
  | _ :: a', _ :: b' -> lemma_same_ids a' b'
  | _, _ -> ()

let same_node (n m:sort_node) : bool =
  match n, m with
  | NodeBase a, NodeBase b -> a = b
  | NodeArray ds r, NodeArray es q -> if r = q then same_ids ds es else false
  | _, _ -> false

let lemma_same_node (n m:sort_node) : Lemma (same_node n m <==> n == m) =
  match n, m with
  | NodeArray ds _, NodeArray es _ -> lemma_same_ids ds es
  | _, _ -> ()

(* The first candidate of `bucket` equal to `n`, `cost` units per candidate compared. *)
let rec find_node (n:sort_node) (cost work:nat) (bucket:list (nat & sort_node))
  : Tot (option (option nat & nat)) (decreases bucket) =
  match bucket with
  | [] -> Some (None, work)
  | (c, m) :: rest ->
    if work < cost then None
    else if same_node m n then Some (Some c, work - cost)
    else find_node n cost (work - cost) rest

let rec lemma_find_node (n:sort_node) (cost work:nat) (bucket:list (nat & sort_node))
  : Lemma (ensures (match find_node n cost work bucket with
                    | Some (Some c, _) -> L.mem (c, n) bucket
                    | Some (None, _) -> forall (c:nat). ~(L.mem (c, n) bucket)
                    | None -> True))
          (decreases bucket)
  = match bucket with
    | [] -> ()
    | (c, m) :: rest ->
      lemma_same_node m n;
      if work >= cost && not (same_node m n) then lemma_find_node n cost (work - cost) rest

let insert_node (t:sort_table) (n:sort_node) (key:nat) (b:list (nat & sort_node)) : sort_table =
  { nodes = I.index_put t.nodes t.node_count n;
    node_count = t.node_count + 1;
    buckets = I.index_put t.buckets key ((t.node_count, n) :: b) }

let fresh_node (t:sort_table) (n:sort_node) : prop =
  valid_table t /\ children_below n t.node_count /\ (forall (c:nat). ~(L.mem (c, n) (bucket_of t (node_key n))))

noextract
let inserted (t:sort_table) (n:sort_node) : sort_table = insert_node t n (node_key n) (bucket_of t (node_key n))

let lemma_inserted_node (t:sort_table) (n:sort_node) (i:nat)
  : Lemma (node_of (inserted t n) i == (if i = t.node_count then Some n else node_of t i))
  = ()

let lemma_inserted_bucket (t:sort_table) (n:sort_node) (k:nat)
  : Lemma (bucket_of (inserted t n) k ==
           (if k = node_key n then (t.node_count, n) :: bucket_of t (node_key n) else bucket_of t k))
  = ()

let lemma_insert_well_founded_at (t:sort_table) (n:sort_node) (i:nat)
  : Lemma (requires fresh_node t n /\ i <= t.node_count)
          (ensures Some? (node_of (inserted t n) i) /\ children_below (Some?.v (node_of (inserted t n) i)) i)
  = lemma_inserted_node t n i

let lemma_insert_well_founded (t:sort_table) (n:sort_node)
  : Lemma (requires fresh_node t n) (ensures well_founded (inserted t n))
  = let t' = inserted t n in
    introduce forall (i:nat). i < t'.node_count ==> Some? (node_of t' i) /\ children_below (Some?.v (node_of t' i)) i
    with FStar.Classical.move_requires (lemma_insert_well_founded_at t n) i

let lemma_insert_distinct_pair (t:sort_table) (n:sort_node) (i j:nat)
  : Lemma (requires fresh_node t n /\ i <= t.node_count /\ j <= t.node_count /\
                    node_of (inserted t n) i == node_of (inserted t n) j)
          (ensures i == j)
  = let c = t.node_count in
    if i = c && j < c then assert (L.mem (j, n) (bucket_of t (node_key n)))
    else if j = c && i < c then assert (L.mem (i, n) (bucket_of t (node_key n)))

let lemma_insert_distinct (t:sort_table) (n:sort_node)
  : Lemma (requires fresh_node t n) (ensures distinct_nodes (inserted t n))
  = let t' = inserted t n in
    introduce forall (i j:nat). i < t'.node_count /\ j < t'.node_count /\ node_of t' i == node_of t' j ==> i == j
    with FStar.Classical.move_requires (lemma_insert_distinct_pair t n i) j

let lemma_insert_complete_at (t:sort_table) (n:sort_node) (i:nat)
  : Lemma (requires fresh_node t n /\ i <= t.node_count)
          (ensures Some? (node_of (inserted t n) i) /\
                   L.mem (i, Some?.v (node_of (inserted t n) i))
                         (bucket_of (inserted t n) (node_key (Some?.v (node_of (inserted t n) i)))))
  = if i < t.node_count then
      (let m = Some?.v (node_of t i) in assert (L.mem (i, m) (bucket_of t (node_key m))))

let lemma_insert_complete (t:sort_table) (n:sort_node)
  : Lemma (requires fresh_node t n) (ensures complete_buckets (inserted t n))
  = let t' = inserted t n in
    introduce forall (i:nat). i < t'.node_count /\ Some? (node_of t' i) ==>
      L.mem (i, Some?.v (node_of t' i)) (bucket_of t' (node_key (Some?.v (node_of t' i))))
    with FStar.Classical.move_requires (lemma_insert_complete_at t n) i

let lemma_insert_sound_at (t:sort_table) (n:sort_node) (k c:nat) (m:sort_node)
  : Lemma (requires fresh_node t n /\ L.mem (c, m) (bucket_of (inserted t n) k))
          (ensures c < (inserted t n).node_count /\ node_of (inserted t n) c == Some m)
  = lemma_inserted_bucket t n k;
    lemma_inserted_node t n c;
    if (c, m) <> (t.node_count, n) || k <> node_key n then
      (assert (L.mem (c, m) (bucket_of t k));
       assert (c < t.node_count /\ node_of t c == Some m))

let lemma_insert_sound (t:sort_table) (n:sort_node)
  : Lemma (requires fresh_node t n) (ensures sound_buckets (inserted t n))
  = let t' = inserted t n in
    introduce forall (k c:nat) (m:sort_node). L.mem (c, m) (bucket_of t' k) ==> c < t'.node_count /\ node_of t' c == Some m
    with FStar.Classical.move_requires (lemma_insert_sound_at t n k c) m

noeq
type interned =
  | Interned : table:sort_table -> id:nat -> work:nat -> store:nat -> interned
  | InternExhausted : phase:budget_phase -> interned

(* `n` itself if it is stored, else a new node; `cost` units per candidate compared. *)
let intern (t:sort_table) (n:sort_node) (key cost work store:nat) : interned =
  match charge work table_units with
  | None -> InternExhausted Preparation
  | Some w ->
    let b = bucket_of t key in
    (match find_node n cost w b with
     | None -> InternExhausted Preparation
     | Some (Some c, w') -> Interned t c w' store
     | Some (None, w') ->
       (match charge w' (2 * table_units) with
        | None -> InternExhausted Preparation
        | Some w'' ->
          (match charge store (2 + 2 * table_units) with
           | None -> InternExhausted Storage
           | Some s' ->
             if t.node_count >= max_sort_nodes then InternExhausted Storage
             else Interned (insert_node t n key b) t.node_count w'' s')))

let interned_ok (t:sort_table) (n:sort_node) (r:interned) : prop =
  match r with
  | Interned t' c _ _ ->
    valid_table t' /\ t.node_count <= t'.node_count /\ agree_below t t' t.node_count /\
    c < t'.node_count /\ node_of t' c == Some n
  | InternExhausted _ -> True

let lemma_intern (t:sort_table) (n:sort_node) (key cost work store:nat)
  : Lemma (requires valid_table t /\ key == node_key n /\ children_below n t.node_count)
          (ensures interned_ok t n (intern t n key cost work store))
  = match charge work table_units with
    | None -> ()
    | Some w ->
      lemma_find_node n cost w (bucket_of t key);
      (match find_node n cost w (bucket_of t key) with
       | Some (None, _) ->
         lemma_insert_well_founded t n;
         lemma_insert_distinct t n;
         lemma_insert_complete t n;
         lemma_insert_sound t n
       | _ -> ())

(* --- Validating an untrusted graph -------------------------------------------------------- *)

let untrusted_id (x:int) : bool = 0 <= x && x < untrusted_id_limit

let resolved (ids:I.index_tree nat) (x:int) : option nat =
  if untrusted_id x then I.index_get ids x else None

noextract
let rec resolved_all (ids:I.index_tree nat) (ds:list int) : Tot (option (list nat)) (decreases ds) =
  match ds with
  | [] -> Some []
  | d :: rest ->
    (match resolved ids d, resolved_all ids rest with
     | Some c, Some cs -> Some (c :: cs)
     | _, _ -> None)

noeq
type step (a:Type) =
  | Continue : value:a -> step a
  | Refused : reason:sort_graph_error -> step a
  | OutOf : phase:budget_phase -> step a

(* The checked ids of the references `ds`, of which there must be `arity`; two
   storage units per reference for the accumulated list and its reversal. *)
let rec resolve_domain (ids:I.index_tree nat) (owner:int) (arity n work store:nat) (acc:list nat) (ds:list int)
  : Tot (step (list nat & nat & nat)) (decreases ds) =
  match ds with
  | [] -> if n = arity then Continue (L.rev acc, work, store) else Refused (WrongArity owner)
  | d :: rest ->
    if n >= arity then Refused (WrongArity owner)
    else (match charge work (1 + table_units) with
          | None -> OutOf Preparation
          | Some w ->
            (match charge store 2 with
             | None -> OutOf Storage
             | Some s ->
               if not (untrusted_id d) then Refused (MalformedId d)
               else (match I.index_get ids d with
                     | None -> Refused (DanglingReference d)
                     | Some c -> resolve_domain ids owner arity (n + 1) w s (c :: acc) rest)))

noeq
type prep_state = { table: sort_table; ids: I.index_tree nat; work: nat; store: nat }

let bind_id (st:prep_state) (x:nat) (t:sort_table) (c work store:nat) : step prep_state =
  match charge work table_units with
  | None -> OutOf Preparation
  | Some w ->
    (match I.index_get st.ids x with
     | Some c0 ->
       if c0 = c then Continue ({ table = t; ids = st.ids; work = w; store = store })
       else Refused (ConflictingDefinition x)
     | None ->
       (match charge w table_units with
        | None -> OutOf Preparation
        | Some w' ->
          (match charge store table_units with
           | None -> OutOf Storage
           | Some s' -> Continue ({ table = t; ids = I.index_put st.ids x c; work = w'; store = s' }))))

let prepare_base ([@@@FStar.Attributes.monomorphize] name_units:name_counter)
                 (st:prep_state) (x:nat) (name:string) (work store:nat)
  : step prep_state =
  match name_units name work with
  | None -> OutOf Preparation
  | Some len ->
    (match intern st.table (NodeBase name) (len % bucket_count) (1 + len) (work - len) store with
     | InternExhausted p -> OutOf p
     | Interned t c w s -> bind_id st x t c w s)

let array_step (st:prep_state) (x:nat) (arity:nat) (cs:list nat) (cr work store:nat) : step prep_state =
  match intern st.table (NodeArray cs cr) (mix (ids_key 1 cs) cr) (2 + arity) work store with
  | InternExhausted p -> OutOf p
  | Interned t c w s -> bind_id st x t c w s

let prepare_array (st:prep_state) (x:nat) (arity:nat) (ds:list int) (r:int) (work store:nat)
  : step prep_state =
  match resolve_domain st.ids x arity 0 work store [] ds with
  | Refused err -> Refused err
  | OutOf p -> OutOf p
  | Continue (cs, w, s) ->
    (match charge w (1 + table_units) with
     | None -> OutOf Preparation
     | Some w1 ->
       if not (untrusted_id r) then Refused (MalformedId r)
       else
         (match I.index_get st.ids r with
          | None -> Refused (DanglingReference r)
          | Some cr -> array_step st x arity cs cr w1 s))

(* One preparation unit to read the entry and one storage unit for the state it yields. *)
let prepare_entry ([@@@FStar.Attributes.monomorphize] name_units:name_counter)
                  (st:prep_state) (e:raw_sort)
  : step prep_state =
  match charge st.work 1, charge st.store 1 with
  | None, _ -> OutOf Preparation
  | _, None -> OutOf Storage
  | Some w, Some s ->
    let x = raw_id e in
    if not (untrusted_id x) then Refused (MalformedId x)
    else
      (match e with
       | RawBase _ name -> prepare_base name_units st x name w s
       | RawArray _ arity ds r -> if arity < 0 then Refused (WrongArity x) else prepare_array st x arity ds r w s)

let rec prepare_entries ([@@@FStar.Attributes.monomorphize] name_units:name_counter)
                        (st:prep_state) (raw:list raw_sort)
  : Tot (step prep_state) (decreases raw) =
  match raw with
  | [] -> Continue st
  | e :: rest ->
    (match prepare_entry name_units st e with
     | Continue st' -> prepare_entries name_units st' rest
     | Refused err -> Refused err
     | OutOf p -> OutOf p)

let ids_below (ids:I.index_tree nat) (bound:nat) : prop =
  forall (x:nat). Some? (I.index_get ids x) ==> Some?.v (I.index_get ids x) < bound

type id_map (g:checked_sort_graph) = m:I.index_tree nat{ids_below m g.node_count}

noeq
type sort_graph_result =
  | Prepared : graph:checked_sort_graph -> ids:id_map graph -> left:sort_budget -> sort_graph_result
  | InvalidSortGraph : reason:sort_graph_error -> sort_graph_result
  | Exhausted : phase:budget_phase -> sort_graph_result

let empty_table : sort_table = { nodes = I.Empty; node_count = 0; buckets = I.Empty }

let initial_state (budget:sort_budget) : prep_state =
  { table = empty_table; ids = I.Empty; work = budget.preparation; store = budget.storage }

let state_ok (st:prep_state) : prop = valid_table st.table /\ ids_below st.ids st.table.node_count

let grows (st st':prep_state) : prop =
  st.table.node_count <= st'.table.node_count /\
  agree_below st.table st'.table st.table.node_count /\
  (forall (x:nat). Some? (I.index_get st.ids x) ==> I.index_get st'.ids x == I.index_get st.ids x)

(* The meaning of one raw entry: its id resolves to a checked id denoting
   exactly its name, or its ordered domain and range. *)
let entry_reflected (t:sort_table) (ids:I.index_tree nat) (e:raw_sort) : prop =
  match e with
  | RawBase x name ->
    (match resolved ids x with Some c -> interp_node t c == BaseSort name | None -> False)
  | RawArray x arity ds r ->
    arity == L.length ds /\
    (match resolved ids x, resolved_all ids ds, resolved ids r with
     | Some c, Some cs, Some cr -> interp_node t c == ArraySort (L.map (interp_node t) cs) (interp_node t cr)
     | _, _, _ -> False)

let lemma_initial_state (budget:sort_budget) : Lemma (state_ok (initial_state budget)) = ()

let rec lemma_resolve_domain (ids:I.index_tree nat) (owner:int) (arity n work store:nat) (acc:list nat) (ds:list int)
  : Lemma (ensures (match resolve_domain ids owner arity n work store acc ds with
                    | Continue (cs, _, _) ->
                      n + L.length ds == arity /\
                      (match resolved_all ids ds with Some r -> cs == L.append (L.rev acc) r | None -> False)
                    | _ -> True))
          (decreases ds)
  = match ds with
    | [] -> L.append_l_nil (L.rev acc)
    | d :: rest ->
      if n < arity && work >= 1 + table_units && store >= 2 && untrusted_id d && Some? (I.index_get ids d) then begin
        let c = Some?.v (I.index_get ids d) in
        lemma_resolve_domain ids owner arity (n + 1) (work - (1 + table_units)) (store - 2) (c :: acc) rest;
        Z3List.lemma_rev_cons c acc;
        match resolved_all ids rest with
        | Some r -> L.append_assoc (L.rev acc) [c] r
        | None -> ()
      end

let rec lemma_resolved_all_below (ids:I.index_tree nat) (bound:nat) (ds:list int)
  : Lemma (requires ids_below ids bound)
          (ensures (match resolved_all ids ds with Some cs -> all_below cs bound | None -> True))
          (decreases ds)
  = match ds with [] -> () | _ :: rest -> lemma_resolved_all_below ids bound rest

let rec lemma_resolved_all_grows (ids ids':I.index_tree nat) (ds:list int)
  : Lemma (requires forall (x:nat). Some? (I.index_get ids x) ==> I.index_get ids' x == I.index_get ids x)
          (ensures Some? (resolved_all ids ds) ==> resolved_all ids' ds == resolved_all ids ds)
          (decreases ds)
  = match ds with [] -> () | _ :: rest -> lemma_resolved_all_grows ids ids' rest

let lemma_ids_widen (ids:I.index_tree nat) (bound bound':nat)
  : Lemma (requires ids_below ids bound /\ bound <= bound') (ensures ids_below ids bound')
  = ()

let lemma_ids_put (ids:I.index_tree nat) (bound x c:nat)
  : Lemma (requires ids_below ids bound /\ c < bound /\ I.index_get ids x == None)
          (ensures ids_below (I.index_put ids x c) bound /\
                   (forall (y:nat). Some? (I.index_get ids y) ==> I.index_get (I.index_put ids x c) y == I.index_get ids y))
  = ()

let bound_ok (st:prep_state) (x:nat) (t:sort_table) (c:nat) (r:step prep_state) : prop =
  match r with
  | Continue st' ->
    st'.table == t /\ ids_below st'.ids t.node_count /\ resolved st'.ids x == Some c /\
    (forall (y:nat). Some? (I.index_get st.ids y) ==> I.index_get st'.ids y == I.index_get st.ids y)
  | _ -> True

let lemma_bind_id (st:prep_state) (x:nat) (t:sort_table) (c work store:nat)
  : Lemma (requires ids_below st.ids t.node_count /\ untrusted_id x /\ c < t.node_count)
          (ensures bound_ok st x t c (bind_id st x t c work store))
  = match charge work table_units with
    | None -> ()
    | Some _ ->
      (match I.index_get st.ids x with
       | Some _ -> ()
       | None -> lemma_ids_put st.ids t.node_count x c)

let lemma_bound_state (st:prep_state) (x:nat) (t:sort_table) (c:nat) (st':prep_state)
  : Lemma (requires state_ok st /\ valid_table t /\ st.table.node_count <= t.node_count /\
                    agree_below st.table t st.table.node_count /\ bound_ok st x t c (Continue st'))
          (ensures state_ok st' /\ grows st st')
  = ()

let prepared_ok (st:prep_state) (e:raw_sort) (r:step prep_state) : prop =
  match r with
  | Continue st' -> state_ok st' /\ grows st st' /\ entry_reflected st'.table st'.ids e
  | _ -> True

let lemma_prepare_base (name_units:name_counter) (st:prep_state) (x:nat) (name:string) (work store:nat)
  : Lemma (requires state_ok st /\ untrusted_id x)
          (ensures prepared_ok st (RawBase x name) (prepare_base name_units st x name work store))
  = match name_units name work with
    | None -> ()
    | Some len ->
      lemma_intern st.table (NodeBase name) (len % bucket_count) (1 + len) (work - len) store;
      (match intern st.table (NodeBase name) (len % bucket_count) (1 + len) (work - len) store with
       | InternExhausted _ -> ()
       | Interned t c w s ->
         lemma_ids_widen st.ids st.table.node_count t.node_count;
         lemma_bind_id st x t c w s;
         lemma_interp_node t c;
         (match bind_id st x t c w s with
          | Continue st' -> lemma_bound_state st x t c st'
          | _ -> ()))

let lemma_array_reflected (st st':prep_state) (x:nat) (arity:nat) (ds:list int) (r:int) (cs:list nat) (cr c:nat)
  : Lemma (requires state_ok st /\ grows st st' /\ valid_table st'.table /\
                    resolved st'.ids x == Some c /\ c < st'.table.node_count /\
                    node_of st'.table c == Some (NodeArray cs cr) /\
                    arity == L.length ds /\ resolved_all st.ids ds == Some cs /\ resolved st.ids r == Some cr)
          (ensures entry_reflected st'.table st'.ids (RawArray x arity ds r))
  = lemma_interp_node st'.table c;
    lemma_resolved_all_grows st.ids st'.ids ds

let lemma_array_step (st:prep_state) (x:nat) (arity:nat) (ds:list int) (r:int) (cs:list nat) (cr work store:nat)
  : Lemma (requires state_ok st /\ untrusted_id x /\ untrusted_id r /\ I.index_get st.ids r == Some cr /\
                    resolved_all st.ids ds == Some cs /\ arity == L.length ds)
          (ensures prepared_ok st (RawArray x arity ds r) (array_step st x arity cs cr work store))
  = lemma_resolved_all_below st.ids st.table.node_count ds;
    let n = NodeArray cs cr in
    let key = mix (ids_key 1 cs) cr in
    lemma_intern st.table n key (2 + arity) work store;
    match intern st.table n key (2 + arity) work store with
    | Interned t c w s ->
      lemma_ids_widen st.ids st.table.node_count t.node_count;
      lemma_bind_id st x t c w s;
      (match bind_id st x t c w s with
       | Continue st' -> lemma_bound_state st x t c st'; lemma_array_reflected st st' x arity ds r cs cr c
       | _ -> ())
    | InternExhausted _ -> ()

let lemma_prepare_array (st:prep_state) (x:nat) (arity:nat) (ds:list int) (r:int) (work store:nat)
  : Lemma (requires state_ok st /\ untrusted_id x)
          (ensures prepared_ok st (RawArray x arity ds r) (prepare_array st x arity ds r work store))
  = lemma_resolve_domain st.ids x arity 0 work store [] ds;
    match resolve_domain st.ids x arity 0 work store [] ds with
    | Continue (cs, w, s) ->
      assert (resolved_all st.ids ds == Some cs);
      (match charge w (1 + table_units) with
       | Some w1 ->
         if untrusted_id r && Some? (I.index_get st.ids r) then
           lemma_array_step st x arity ds r cs (Some?.v (I.index_get st.ids r)) w1 s
       | None -> ())
    | _ -> ()

let lemma_prepare_entry (name_units:name_counter) (st:prep_state) (e:raw_sort)
  : Lemma (requires state_ok st) (ensures prepared_ok st e (prepare_entry name_units st e))
  = match charge st.work 1, charge st.store 1 with
    | Some w, Some s ->
      let x = raw_id e in
      if untrusted_id x then
        (match e with
         | RawBase _ name -> lemma_prepare_base name_units st x name w s
         | RawArray _ arity ds r -> if arity >= 0 then lemma_prepare_array st x arity ds r w s)
    | _, _ -> ()

let lemma_reflected_grows (st st':prep_state) (e:raw_sort)
  : Lemma (requires state_ok st /\ grows st st' /\ entry_reflected st.table st.ids e)
          (ensures entry_reflected st'.table st'.ids e)
  = let bound = st.table.node_count in
    match e with
    | RawBase x _ -> lemma_interp_agree st.table st'.table bound (Some?.v (resolved st.ids x))
    | RawArray x _ ds r ->
      lemma_interp_agree st.table st'.table bound (Some?.v (resolved st.ids x));
      lemma_interp_agree st.table st'.table bound (Some?.v (resolved st.ids r));
      lemma_resolved_all_below st.ids bound ds;
      lemma_resolved_all_grows st.ids st'.ids ds;
      lemma_map_agree st.table st'.table bound (Some?.v (resolved_all st.ids ds))

let lemma_grows_trans (st1 st2 st3:prep_state)
  : Lemma (requires grows st1 st2 /\ grows st2 st3) (ensures grows st1 st3)
  = ()

let rec lemma_prepare_entries (name_units:name_counter) (st:prep_state) (raw:list raw_sort)
  : Lemma (requires state_ok st)
          (ensures (match prepare_entries name_units st raw with
                    | Continue st' ->
                      state_ok st' /\ grows st st' /\
                      (forall (e:raw_sort). L.mem e raw ==> entry_reflected st'.table st'.ids e)
                    | _ -> True))
          (decreases raw)
  = match raw with
    | [] -> ()
    | e :: rest ->
      lemma_prepare_entry name_units st e;
      (match prepare_entry name_units st e with
       | Continue st1 ->
         lemma_prepare_entries name_units st1 rest;
         (match prepare_entries name_units st1 rest with
          | Continue st2 -> lemma_reflected_grows st1 st2 e; lemma_grows_trans st st1 st2
          | _ -> ())
       | _ -> ())

(* --- The boundary ------------------------------------------------------------------------- *)

let validate_sort_graph ([@@@FStar.Attributes.monomorphize] name_units:name_counter)
                        (raw:list raw_sort) (budget:sort_budget)
  : sort_graph_result =
  match prepare_entries name_units (initial_state budget) raw with
  | Continue st ->
    lemma_initial_state budget;
    lemma_prepare_entries name_units (initial_state budget) raw;
    Prepared st.table st.ids { preparation = st.work; storage = st.store }
  | Refused err -> InvalidSortGraph err
  | OutOf p -> Exhausted p

let resolve_id (g:checked_sort_graph) (m:id_map g) (x:int) : option (sort_id g) =
  if untrusted_id x then (match I.index_get m x with Some c -> Some c | None -> None) else None

let lemma_validated (name_units:name_counter) (raw:list raw_sort) (budget:sort_budget)
  : Lemma (match validate_sort_graph name_units raw budget with
           | Prepared g m _ -> forall (e:raw_sort). L.mem e raw ==> entry_reflected g m e
           | _ -> True)
  = lemma_initial_state budget;
    lemma_prepare_entries name_units (initial_state budget) raw
