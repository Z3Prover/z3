module Z3DagScopeInterning
(* Self-contained re-statement of the PR's scope interning (Z3DagScope.fst @ f6256d3):
   scope_table, find_cell, scope_ids, scopes_ok, push, new_scopes.
   Only changes: CS.table_units / T.phase replaced by a local positive constant / local type,
   CS.all_below inlined. Self-contained (index_tree inlined). *)
module L = FStar.List.Tot

(* Verbatim copy of index_tree / index_get / index_put / lemma_index_put from base Z3ProofIndex.fst,
   inlined because the pinned fstar.exe rejects the base module's FStar.Attributes.custard_inline. *)
noeq type index_tree (a:Type) =
  | Empty : index_tree a
  | Branch : option a -> index_tree a -> index_tree a -> index_tree a

let rec index_get (#a:Type) (tree:index_tree a) (key:nat) : Tot (option a) (decreases key) =
  match tree with
  | Empty -> None
  | Branch value left right ->
    if key = 0 then value
    else if key % 2 = 1 then index_get left ((key - 1) / 2)
    else index_get right ((key - 1) / 2)

let rec index_put (#a:Type) (tree:index_tree a) (key:nat) (value:a) : Tot (index_tree a) (decreases key) =
  let old, left, right = match tree with | Empty -> None, Empty, Empty | Branch old left right -> old, left, right in
  if key = 0 then Branch (Some value) left right
  else if key % 2 = 1 then Branch old (index_put left ((key - 1) / 2) value) right
  else Branch old left (index_put right ((key - 1) / 2) value)

let rec lemma_index_put (#a:Type) (tree:index_tree a) (key:nat) (value:a) (query:nat)
  : Lemma (index_get (index_put tree key value) query == (if query = key then Some value else index_get tree query))
          (decreases key) =
  if key = 0 || query = 0 then ()
  else
    let left, right = match tree with Empty -> Empty, Empty | Branch _ left right -> left, right in
    if key % 2 = query % 2 then
      lemma_index_put (if key % 2 = 1 then left else right) ((key - 1) / 2) value ((query - 1) / 2)

let tu : n:nat{n > 0} = 1 (* any positive unit; lemmas below quantify over it only via work/store arithmetic *)
type phase = | Validation | Storage

noeq type scope_table = {
  cells: index_tree (nat & nat);
  index: index_tree (index_tree nat);
  count: nat;
}
let empty_scopes : scope_table = { cells = Empty; index = Empty; count = 1 }
let cell (st:scope_table) (i:nat) : option (nat & nat) = index_get st.cells i
let find_cell (st:scope_table) (h t:nat) : option nat =
  match index_get st.index t with
  | Some inner -> index_get inner h
  | None -> None

let rec scope_ids (st:scope_table) (i:nat) : Tot (list nat) (decreases i) =
  if i = 0 then []
  else match cell st i with
    | Some (h, t) -> if t < i then h :: scope_ids st t else []
    | None -> []

let scopes_ok (st:scope_table) (bound:nat) : prop =
  st.count >= 1 /\
  (forall (i:nat). 0 < i /\ i < st.count ==>
     (match cell st i with
      | Some (h, t) -> t < i /\ h < bound /\ find_cell st h t == Some i
      | None -> False)) /\
  (forall (h t i:nat). find_cell st h t == Some i ==> 0 < i /\ i < st.count /\ cell st i == Some (h, t))

let scopes_grow (st st':scope_table) : prop =
  st.count <= st'.count /\ (forall (i:nat). i < st.count ==> cell st' i == cell st i)

let rec lemma_scope_ids_grow (st st':scope_table) (i:nat)
  : Lemma (requires scopes_grow st st' /\ i < st.count) (ensures scope_ids st' i == scope_ids st i) (decreases i)
  = if i = 0 then ()
    else match cell st i with
      | Some (h, t) -> if t < i then lemma_scope_ids_grow st st' t
      | None -> ()

(* Obligation 1: interning is exact (one id per scope). *)
let rec lemma_scope_canonical (st:scope_table) (bound i j:nat)
  : Lemma (requires scopes_ok st bound /\ i < st.count /\ j < st.count /\ scope_ids st i == scope_ids st j)
          (ensures i == j) (decreases i)
  = if i = 0 || j = 0 then ()
    else match cell st i, cell st j with
      | Some (h, t), Some (h', t') -> lemma_scope_canonical st bound t t'
      | _, _ -> ()

noeq type pushed =
  | Pushed : table:scope_table -> id:nat -> work:nat -> store:nat -> pushed
  | PushExhausted : phase:phase -> pushed

let push (st:scope_table) (h t:nat) (work store:nat) : r:pushed{Pushed? r ==> Pushed?.work r <= work} =
  if work < 2 * tu then PushExhausted Validation
  else match find_cell st h t with
    | Some i -> Pushed st i (work - 2 * tu) store
    | None ->
      if work < 5 * tu then PushExhausted Validation
      else if store < 3 + 3 * tu then PushExhausted Storage
      else
        let i = st.count in
        let inner = match index_get st.index t with Some inner -> inner | None -> Empty in
        Pushed ({ cells = index_put st.cells i (h, t); index = index_put st.index t (index_put inner h i);
                  count = i + 1 }) i (work - 5 * tu) (store - (3 + 3 * tu))

let push_ok (st:scope_table) (bound h t:nat) (r:pushed) : prop =
  match r with
  | Pushed st' i _ _ -> scopes_ok st' bound /\ scopes_grow st st' /\ i < st'.count /\ scope_ids st' i == h :: scope_ids st' t
  | PushExhausted _ -> True

let new_scopes (st:scope_table) (h t:nat) : scope_table =
  let i = st.count in
  let inner = match index_get st.index t with Some inner -> inner | None -> Empty in
  { cells = index_put st.cells i (h, t); index = index_put st.index t (index_put inner h i); count = i + 1 }

let lemma_new_cells (st:scope_table) (h t j:nat)
  : Lemma (cell (new_scopes st h t) j == (if j = st.count then Some (h, t) else cell st j))
  = lemma_index_put st.cells st.count (h, t) j

let lemma_new_find (st:scope_table) (h t h' t':nat)
  : Lemma (find_cell (new_scopes st h t) h' t' == (if h' = h && t' = t then Some st.count else find_cell st h' t'))
  = let inner = match index_get st.index t with Some inner -> inner | None -> Empty in
    lemma_index_put st.index t (index_put inner h st.count) t';
    lemma_index_put inner h st.count h'

let lemma_new_grows (st:scope_table) (h t:nat)
  : Lemma (scopes_grow st (new_scopes st h t))
  = FStar.Classical.forall_intro (lemma_new_cells st h t)

let lemma_new_ok (st:scope_table) (bound h t:nat)
  : Lemma (requires scopes_ok st bound /\ h < bound /\ t < st.count /\ find_cell st h t == None)
          (ensures scopes_ok (new_scopes st h t) bound)
  = let st' = new_scopes st h t in
    let i = st.count in
    let a1 (j:nat) : Lemma (requires 0 < j /\ j < st'.count)
                          (ensures (match cell st' j with
                                    | Some (h1, t1) -> t1 < j /\ h1 < bound /\ find_cell st' h1 t1 == Some j
                                    | None -> False))
      = lemma_new_cells st h t j;
        if j = i then lemma_new_find st h t h t
        else begin
          assert (j < st.count);
          match cell st j with
          | Some (h1, t1) -> assert (find_cell st h1 t1 == Some j); lemma_new_find st h t h1 t1
          | None -> ()
        end in
    let a2 (h1 t1 j:nat) : Lemma (requires find_cell st' h1 t1 == Some j)
                                (ensures 0 < j /\ j < st'.count /\ cell st' j == Some (h1, t1))
      = lemma_new_find st h t h1 t1;
        lemma_new_cells st h t j;
        if h1 = h && t1 = t then ()
        else assert (0 < j /\ j < st.count /\ cell st j == Some (h1, t1)) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires a1);
    FStar.Classical.forall_intro_3 (fun h1 t1 j -> FStar.Classical.move_requires (a2 h1 t1) j)

(* Obligation 2: push preserves the table invariant and denotes h :: scope; Obligation 3: work never increases (in the refinement type). *)
let lemma_push (st:scope_table) (bound h t:nat) (work store:nat)
  : Lemma (requires scopes_ok st bound /\ h < bound /\ t < st.count) (ensures push_ok st bound h t (push st h t work store))
  = match find_cell st h t with
    | Some i -> assert (0 < i /\ i < st.count /\ cell st i == Some (h, t)); assert (t < i)
    | None ->
      if work < 5 * tu || store < 3 + 3 * tu then ()
      else begin
        let st' = new_scopes st h t in
        assert (push st h t work store == Pushed st' st.count (work - 5 * tu) (store - (3 + 3 * tu)));
        lemma_new_ok st bound h t;
        lemma_new_grows st h t;
        lemma_scope_ids_grow st st' t;
        lemma_new_cells st h t st.count
      end
