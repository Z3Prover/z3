(*
   Z3DagScope.fst

   The memoised scope check of `Z3CheckedGraph` nodes. A scope (a list of
   checked sort ids, `Var 0` first) is interned into a table of cons cells,
   one id per distinct scope (`push` finds an existing cell by its head and
   tail ids, exactly; `lemma_scope_canonical`), so a complete ordered typed
   scope has one id.

   `walk` checks nodes at scope ids over an explicit worklist and records a
   node/scope pair in the memo only when its own conditions hold and, for an
   application or a quantifier, its children are already recorded at the
   scope they are checked at (re-read when the pair is closed). `memo_ok`: a
   recorded pair `(x, s)` means `Z3Definitions.scoped` of the scope `s`
   denotes and the expression stored at `x` -- a structural fact, not a
   semantic one, valid for the graph and scope table it was recorded with
   and their extensions. A failed or exhausted walk returns no memo, so
   nothing it recorded is kept.

   Units, charged before the step they pay for. Validation: one per frame,
   `2 table_units` per memo lookup or scope-cell lookup, `table_units` per
   cell walked to a variable's binder, `3 table_units` per scope cell
   created. Storage: one cell per frame pushed, `2 + 2 table_units` per memo
   entry and `3 + 3 table_units` per scope cell. The units are an abstract
   count, not a time or memory bound.
*)
module Z3DagScope

open Z3AstTheory
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module T = Z3CheckedTerms
module CG = Z3CheckedGraph
module D = Z3Definitions

let tu : nat = CS.table_units

(* --- Scope ids -------------------------------------------------------------------------------- *)

noeq
type scope_table = {
  cells: I.index_tree (nat & nat);         (* id -> (head sort id, tail scope id) *)
  index: I.index_tree (I.index_tree nat);  (* tail -> head -> id *)
  count: nat;                              (* ids below count; 0 is the empty scope *)
}

let empty_scopes : scope_table = { cells = I.Empty; index = I.Empty; count = 1 }

let cell (st:scope_table) (i:nat) : option (nat & nat) = I.index_get st.cells i

let find_cell (st:scope_table) (h t:nat) : option nat =
  match I.index_get st.index t with
  | Some inner -> I.index_get inner h
  | None -> None

noextract
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

let rec lemma_scope_ids_below (st:scope_table) (bound i:nat)
  : Lemma (requires scopes_ok st bound /\ i < st.count) (ensures CS.all_below (scope_ids st i) bound) (decreases i)
  = if i = 0 then ()
    else match cell st i with
      | Some (h, t) -> lemma_scope_ids_below st bound t
      | None -> ()

(* Interning is exact: one id per scope. *)
let rec lemma_scope_canonical (st:scope_table) (bound i j:nat)
  : Lemma (requires scopes_ok st bound /\ i < st.count /\ j < st.count /\ scope_ids st i == scope_ids st j)
          (ensures i == j) (decreases i)
  = if i = 0 || j = 0 then ()
    else match cell st i, cell st j with
      | Some (h, t), Some (h', t') -> lemma_scope_canonical st bound t t'
      | _, _ -> ()

noeq
type pushed =
  | Pushed : table:scope_table -> id:nat -> work:nat -> store:nat -> pushed
  | PushExhausted : phase:T.phase -> pushed

(* The scope `h :: t`. *)
let push (st:scope_table) (h t:nat) (work store:nat) : r:pushed{Pushed? r ==> Pushed?.work r <= work} =
  if work < 2 * tu then PushExhausted T.Validation
  else match find_cell st h t with
    | Some i -> Pushed st i (work - 2 * tu) store
    | None ->
      if work < 5 * tu then PushExhausted T.Validation
      else if store < 3 + 3 * tu then PushExhausted T.Storage
      else
        let i = st.count in
        let inner = match I.index_get st.index t with Some inner -> inner | None -> I.Empty in
        Pushed ({ cells = I.index_put st.cells i (h, t); index = I.index_put st.index t (I.index_put inner h i);
                  count = i + 1 }) i (work - 5 * tu) (store - (3 + 3 * tu))

let push_ok (st:scope_table) (bound h t:nat) (r:pushed) : prop =
  match r with
  | Pushed st' i _ _ -> scopes_ok st' bound /\ scopes_grow st st' /\ i < st'.count /\ scope_ids st' i == h :: scope_ids st' t
  | PushExhausted _ -> True

let lemma_push_found (st:scope_table) (bound h t i:nat)
  : Lemma (requires scopes_ok st bound /\ find_cell st h t == Some i)
          (ensures scopes_grow st st /\ i < st.count /\ scope_ids st i == h :: scope_ids st t)
  = assert (0 < i /\ i < st.count /\ cell st i == Some (h, t));
    assert (t < i)

let new_scopes (st:scope_table) (h t:nat) : scope_table =
  let i = st.count in
  let inner = match I.index_get st.index t with Some inner -> inner | None -> I.Empty in
  { cells = I.index_put st.cells i (h, t); index = I.index_put st.index t (I.index_put inner h i); count = i + 1 }

let lemma_new_cells (st:scope_table) (h t j:nat)
  : Lemma (cell (new_scopes st h t) j == (if j = st.count then Some (h, t) else cell st j))
  = I.lemma_index_put st.cells st.count (h, t) j

let lemma_new_find (st:scope_table) (h t h' t':nat)
  : Lemma (find_cell (new_scopes st h t) h' t' == (if h' = h && t' = t then Some st.count else find_cell st h' t'))
  = let inner = match I.index_get st.index t with Some inner -> inner | None -> I.Empty in
    I.lemma_index_put st.index t (I.index_put inner h st.count) t';
    I.lemma_index_put inner h st.count h'

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
          | Some (h1, t1) ->
            assert (find_cell st h1 t1 == Some j);
            lemma_new_find st h t h1 t1
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

let lemma_push (st:scope_table) (bound h t:nat) (work store:nat)
  : Lemma (requires scopes_ok st bound /\ h < bound /\ t < st.count) (ensures push_ok st bound h t (push st h t work store))
  = match find_cell st h t with
    | Some i -> lemma_push_found st bound h t i
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

(* `L.rev bs @ s`: the scope of a body under the binders `bs` (`Var 0` the last). *)
let rec under (st:scope_table) (bs:list nat) (s:nat) (work store:nat)
  : Tot (r:pushed{Pushed? r ==> Pushed?.work r <= work}) (decreases bs) =
  match bs with
  | [] -> Pushed st s work store
  | b :: rest ->
    (match push st b s work store with
     | Pushed st' s' w' st'' -> under st' rest s' w' st''
     | PushExhausted p -> PushExhausted p)

let under_ok (st:scope_table) (bound:nat) (bs:list nat) (s:nat) (r:pushed) : prop =
  match r with
  | Pushed st' i _ _ ->
    scopes_ok st' bound /\ scopes_grow st st' /\ i < st'.count /\ scope_ids st' i == L.append (L.rev bs) (scope_ids st s)
  | PushExhausted _ -> True

let rec lemma_under (st:scope_table) (bound:nat) (bs:list nat) (s:nat) (work store:nat)
  : Lemma (requires scopes_ok st bound /\ CS.all_below bs bound /\ s < st.count)
          (ensures under_ok st bound bs s (under st bs s work store)) (decreases bs)
  = match bs with
    | [] -> ()
    | b :: rest ->
      lemma_push st bound b s work store;
      (match push st b s work store with
       | Pushed st1 s1 w1 r1 ->
         lemma_scope_ids_grow st st1 s;
         lemma_under st1 bound rest s1 w1 r1;
         (match under st1 rest s1 w1 r1 with
          | Pushed st2 i _ _ ->
            lemma_scope_ids_grow st1 st2 s1;
            Z3List.lemma_rev_cons b rest;
            L.append_assoc (L.rev rest) [b] (scope_ids st s)
          | _ -> ())
       | _ -> ())

(* The scope of the ids `ids` (`Var 0` first): its cells pushed last id first. *)
let intern_scope (st:scope_table) (ids:list nat) (work store:nat) : pushed =
  if work < L.length ids then PushExhausted T.Validation
  else under st (L.rev ids) 0 (work - L.length ids) store

let lemma_intern_scope (st:scope_table) (bound:nat) (ids:list nat) (work store:nat)
  : Lemma (requires scopes_ok st bound /\ CS.all_below ids bound)
          (ensures (match intern_scope st ids work store with
                    | Pushed st' i _ _ -> scopes_ok st' bound /\ scopes_grow st st' /\ i < st'.count /\ scope_ids st' i == ids
                    | PushExhausted _ -> True))
  = if work < L.length ids then ()
    else begin
      T.lemma_all_below_rev ids bound;
      lemma_under st bound (L.rev ids) 0 (work - L.length ids) store;
      FStar.List.Tot.Properties.rev_involutive ids;
      L.append_l_nil ids
    end

(* --- The memo of checked node/scope pairs ---------------------------------------------------------- *)

type memo = I.index_tree (I.index_tree unit)

let memo_has (m:memo) (x s:nat) : bool =
  match I.index_get m x with
  | Some inner -> Some? (I.index_get inner s)
  | None -> false

let memo_put (m:memo) (x s:nat) : memo =
  let inner = match I.index_get m x with Some inner -> inner | None -> I.Empty in
  I.index_put m x (I.index_put inner s ())

let lemma_memo_put (m:memo) (x s y r:nat)
  : Lemma (memo_has (memo_put m x s) y r == ((y = x && r = s) || memo_has m y r))
  = let inner = match I.index_get m x with Some inner -> inner | None -> I.Empty in
    I.lemma_index_put m x (I.index_put inner s ()) y;
    I.lemma_index_put inner s () r

noextract
let scope_sorts (g:CG.cgraph) (st:scope_table) (s:nat) : list sort = L.map (CG.interp g) (scope_ids st s)

let memo_ok (g:CG.cgraph) (st:scope_table) (m:memo) : prop =
  forall (x s:nat). memo_has m x s ==>
    x < CG.node_count g /\ s < st.count /\
    (match CG.value_of g x with Some v -> D.scoped (scope_sorts g st s) v == true | None -> False)

let lemma_memo_empty (g:CG.cgraph) (st:scope_table) : Lemma (memo_ok g st I.Empty) = ()

(* Growing the scope table and the graph keeps every recorded fact. *)
let lemma_memo_grows (g g':CG.cgraph) (st st':scope_table) (m:memo)
  : Lemma (requires memo_ok g st m /\ CG.cgrows g g' /\ scopes_ok st (CG.sort_count g) /\ scopes_grow st st')
          (ensures memo_ok g' st' m)
  = let aux (x s:nat) : Lemma (requires memo_has m x s) (ensures
        x < CG.node_count g' /\ s < st'.count /\
        (match CG.value_of g' x with Some v -> D.scoped (scope_sorts g' st' s) v == true | None -> False))
      = lemma_scope_ids_grow st st' s;
        lemma_scope_ids_below st (CG.sort_count g) s;
        CS.lemma_map_agree g.CG.terms.T.sorts g'.CG.terms.T.sorts (CG.sort_count g) (scope_ids st s) in
    FStar.Classical.forall_intro_2 (fun x s -> FStar.Classical.move_requires (aux x) s)

(* --- Reading a scope ------------------------------------------------------------------------------- *)

(* The `n`-th sort id of scope `s`, one cell lookup per step; `None` beyond `work`. *)
let rec scope_nth (st:scope_table) (s n work:nat)
  : Tot (r:option (option nat & nat){Some? r ==> snd (Some?.v r) <= work}) (decreases n) =
  if work < tu then None
  else if s = 0 then Some (None, work - tu)
  else match cell st s with
    | Some (h, t) ->
      if t >= s then Some (None, work - tu)
      else if n = 0 then Some (Some h, work - tu)
      else scope_nth st t (n - 1) (work - tu)
    | None -> Some (None, work - tu)

let rec lemma_scope_nth (st:scope_table) (s n work:nat)
  : Lemma (ensures (match scope_nth st s n work with
                    | Some (Some j, _) -> n < L.length (scope_ids st s) /\ L.index (scope_ids st s) n == j
                    | _ -> True))
          (decreases n)
  = if work < tu || s = 0 then ()
    else match cell st s with
      | Some (h, t) -> if n > 0 && t < s then lemma_scope_nth st t (n - 1) (work - tu)
      | None -> ()

let rec lemma_index_map (#a #b:Type) (f:a -> b) (l:list a) (n:nat)
  : Lemma (requires n < L.length l) (ensures n < L.length (L.map f l) /\ L.index (L.map f l) n == f (L.index l n))
          (decreases l)
  = match l with
    | _ :: rest -> if n > 0 then lemma_index_map f rest (n - 1)

(* --- The walk ------------------------------------------------------------------------------------ *)

type frame =
  | Visit : node:nat -> scope:nat -> frame
  | Close : node:nat -> scope:nat -> frame

noeq
type walked =
  | Walked : table:scope_table -> memo:memo -> work:nat -> store:nat -> walked
  | WalkExhausted : phase:T.phase -> walked
  | WalkFailed

let push_visit (s:nat) (acc:list frame) (x:nat) : list frame = Visit x s :: acc

(* `Visit x s` for each `x` of `xs`, in order, before `rest`. *)
let visits (xs:list nat) (s:nat) (rest:list frame) : list frame =
  L.fold_left (push_visit s) rest (L.rev xs)

(* Whether every node of `xs` is recorded at `s`; `None` beyond `work`. *)
let rec all_recorded (m:memo) (xs:list nat) (s work:nat)
  : Tot (r:option (bool & nat){Some? r ==> snd (Some?.v r) <= work}) (decreases xs) =
  match xs with
  | [] -> Some (true, work)
  | x :: rest ->
    if work < 2 * tu then None
    else if memo_has m x s then all_recorded m rest s (work - 2 * tu)
    else Some (false, work - 2 * tu)

let record (m:memo) (x s work store:nat)
  : r:option (memo & nat & nat){Some? r ==> (let (_, w, _) = Some?.v r in w <= work)} =
  if work < 2 * tu then None
  else if store < 2 + 2 * tu then None
  else Some (memo_put m x s, work - 2 * tu, store - (2 + 2 * tu))

noeq
type stepped =
  | Next : table:scope_table -> memo:memo -> work:nat -> store:nat -> frames:list frame -> stepped
  | Stop : result:walked -> stepped

let stop_record (w:nat) : stepped =
  if w < 2 * tu then Stop (WalkExhausted T.Validation) else Stop (WalkExhausted T.Storage)

let visit_step (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s:nat) (rest:list frame)
  : r:stepped{Next? r ==> Next?.work r <= w} =
  if memo_has m x s then Next st m w store rest
  else if x >= CG.node_count g then Stop WalkFailed
  else
    match CG.node_of g x with
    | None -> Stop WalkFailed
    | Some (T.ENVar n i) ->
      (match scope_nth st s n w with
       | None -> Stop (WalkExhausted T.Validation)
       | Some (Some j, w1) ->
         if j <> i then Stop WalkFailed
         else
           (match record m x s w1 store with
            | Some (m', w2, s2) -> Next st m' w2 s2 rest
            | None -> stop_record w1)
       | Some (None, _) -> Stop WalkFailed)
    | Some (T.ENApp ok xs _) ->
      if not ok then Stop WalkFailed
      else
        let k = L.length xs in
        if w < k then Stop (WalkExhausted T.Validation)
        else if store < k + 1 then Stop (WalkExhausted T.Storage)
        else Next st m (w - k) (store - (k + 1)) (visits xs s (Close x s :: rest))
    | Some (T.ENQuant ok bids y _) ->
      if not ok then Stop WalkFailed
      else
        (match under st bids s w store with
         | PushExhausted p -> Stop (WalkExhausted p)
         | Pushed st' s' w' store' ->
           if store' < 2 then Stop (WalkExhausted T.Storage)
           else Next st' m w' (store' - 2) (Visit y s' :: Close x s :: rest))

let close_step (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s:nat) (rest:list frame)
  : r:stepped{Next? r ==> Next?.work r <= w} =
  if x >= CG.node_count g then Stop WalkFailed
  else
    match CG.node_of g x with
    | Some (T.ENApp true xs _) ->
      (match all_recorded m xs s w with
       | None -> Stop (WalkExhausted T.Validation)
       | Some (false, _) -> Stop WalkFailed
       | Some (true, w1) ->
         (match record m x s w1 store with
          | Some (m', w2, s2) -> Next st m' w2 s2 rest
          | None -> stop_record w1))
    | Some (T.ENQuant true bids y _) ->
      (match under st bids s w store with
       | PushExhausted p -> Stop (WalkExhausted p)
       | Pushed st' s' w1 store1 ->
         if w1 < 2 * tu then Stop (WalkExhausted T.Validation)
         else if not (memo_has m y s') then Stop WalkFailed
         else
           (match record m x s (w1 - 2 * tu) store1 with
            | Some (m', w2, s2) -> Next st' m' w2 s2 rest
            | None -> stop_record (w1 - 2 * tu)))
    | _ -> Stop WalkFailed

let walk_step (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (fr:frame) (rest:list frame)
  : r:stepped{Next? r ==> Next?.work r <= w} =
  match fr with
  | Visit x s -> visit_step g st m w store x s rest
  | Close x s -> close_step g st m w store x s rest

let rec walk (g:CG.cgraph) (st:scope_table) (m:memo) (work store:nat) (frames:list frame)
  : Tot walked (decreases work) =
  match frames with
  | [] -> Walked st m work store
  | fr :: rest ->
    if work < 1 + 2 * tu then WalkExhausted T.Validation
    else
      match walk_step g st m (work - (1 + 2 * tu)) store fr rest with
      | Next st' m' w' s' frames' -> walk g st' m' w' s' frames'
      | Stop r -> r

(* --- What a walk earns ----------------------------------------------------------------------------- *)

let rec frames_below (frames:list frame) (bound:nat) : Tot bool (decreases frames) =
  match frames with
  | [] -> true
  | Visit _ s :: rest -> s < bound && frames_below rest bound
  | Close _ s :: rest -> s < bound && frames_below rest bound

let rec lemma_frames_widen (frames:list frame) (b b':nat)
  : Lemma (requires frames_below frames b /\ b <= b') (ensures frames_below frames b') (decreases frames)
  = match frames with [] -> () | _ :: rest -> lemma_frames_widen rest b b'

let rec lemma_fold_visits (s:nat) (rest:list frame) (l:list nat) (b:nat)
  : Lemma (requires s < b /\ frames_below rest b) (ensures frames_below (L.fold_left (push_visit s) rest l) b)
          (decreases l)
  = match l with [] -> () | x :: l' -> lemma_fold_visits s (push_visit s rest x) l' b

let lemma_visits_below (xs:list nat) (s:nat) (rest:list frame) (b:nat)
  : Lemma (requires s < b /\ frames_below rest b) (ensures frames_below (visits xs s rest) b)
  = lemma_fold_visits s rest (L.rev xs) b

let lemma_memo_put_ok (g:CG.cgraph) (st:scope_table) (m:memo) (x s:nat)
  : Lemma (requires memo_ok g st m /\ x < CG.node_count g /\ s < st.count /\
                    (match CG.value_of g x with Some v -> D.scoped (scope_sorts g st s) v == true | None -> False))
          (ensures memo_ok g st (memo_put m x s))
  = let aux (y r:nat) : Lemma (memo_has (memo_put m x s) y r == ((y = x && r = s) || memo_has m y r))
      = lemma_memo_put m x s y r in
    FStar.Classical.forall_intro_2 aux

let rec lemma_all_recorded (g:CG.cgraph) (st:scope_table) (m:memo) (xs:list nat) (s work:nat) (args:list expr)
  : Lemma (requires memo_ok g st m /\ CG.values_of g xs == Some args /\
                    (match all_recorded m xs s work with Some (true, _) -> True | _ -> False))
          (ensures D.scoped_args (scope_sorts g st s) args == true) (decreases xs)
  = match xs, args with
    | x :: rest, a :: args' -> lemma_all_recorded g st m rest s (work - 2 * tu) args'
    | _, _ -> ()

let lemma_var_scoped (g:CG.cgraph) (st:scope_table) (s n:nat) (i j w:nat) (s0:sort)
  : Lemma (requires (match scope_nth st s n w with Some (Some j', _) -> j' == j | _ -> False) /\ j == i /\
                    CG.interp g i == s0)
          (ensures D.scoped (scope_sorts g st s) (Var n s0) == true)
  = lemma_scope_nth st s n w;
    lemma_index_map (CG.interp g) (scope_ids st s) n

let rec lemma_map_rev (#a #b:Type) (f:a -> b) (l:list a)
  : Lemma (ensures L.map f (L.rev l) == L.rev (L.map f l)) (decreases l)
  = match l with
    | [] -> ()
    | x :: rest ->
      lemma_map_rev f rest;
      Z3List.lemma_rev_cons x rest;
      Z3List.lemma_rev_cons (f x) (L.map f rest);
      FStar.List.Tot.Properties.map_append f (L.rev rest) [x]

let lemma_under_sorts (g:CG.cgraph) (st st':scope_table) (bids:list nat) (s s':nat)
  : Lemma (requires scope_ids st' s' == L.append (L.rev bids) (scope_ids st' s))
          (ensures scope_sorts g st' s' == L.append (L.rev (L.map (CG.interp g) bids)) (scope_sorts g st' s))
  = FStar.List.Tot.Properties.map_append (CG.interp g) (L.rev bids) (scope_ids st' s);
    lemma_map_rev (CG.interp g) bids

let lemma_var_record (g:CG.cgraph) (st:scope_table) (m:memo) (x s n i w:nat)
  : Lemma (requires CG.graph_inv g /\ memo_ok g st m /\ x < CG.node_count g /\ s < st.count /\
                    CG.node_of g x == Some (T.ENVar n i) /\
                    (match scope_nth st s n w with Some (Some j, _) -> j == i | _ -> False))
          (ensures memo_ok g st (memo_put m x s))
  = CG.reveal_exact g x;
    match CG.value_of g x with
    | Some (Var n' s0) -> lemma_var_scoped g st s n i i w s0; lemma_memo_put_ok g st m x s
    | _ -> ()

let lemma_app_record (g:CG.cgraph) (st:scope_table) (m:memo) (x s:nat) (xs:list nat) (r w:nat)
  : Lemma (requires CG.graph_inv g /\ memo_ok g st m /\ x < CG.node_count g /\ s < st.count /\
                    CG.node_of g x == Some (T.ENApp true xs r) /\
                    (match all_recorded m xs s w with Some (true, _) -> True | _ -> False))
          (ensures memo_ok g st (memo_put m x s))
  = CG.reveal_exact g x;
    match CG.value_of g x with
    | Some (App f args) -> lemma_all_recorded g st m xs s w args; lemma_memo_put_ok g st m x s
    | _ -> ()

let lemma_quant_record (g:CG.cgraph) (st st':scope_table) (m:memo) (x s:nat) (bids:list nat) (y r s':nat)
  : Lemma (requires CG.graph_inv g /\ memo_ok g st' m /\ x < CG.node_count g /\ s < st.count /\
                    scopes_grow st st' /\ s' < st'.count /\
                    CG.node_of g x == Some (T.ENQuant true bids y r) /\
                    scope_ids st' s' == L.append (L.rev bids) (scope_ids st s) /\ memo_has m y s')
          (ensures memo_ok g st' (memo_put m x s))
  = CG.reveal_exact g x;
    lemma_scope_ids_grow st st' s;
    match CG.value_of g x with
    | Some (Quantifier k bs q b) ->
      lemma_under_sorts g st st' bids s s';
      lemma_memo_put_ok g st' m x s
    | _ -> ()

let walk_ok (g:CG.cgraph) (st:scope_table) (r:walked) : prop =
  match r with
  | Walked st' m' _ _ -> scopes_ok st' (CG.sort_count g) /\ scopes_grow st st' /\ memo_ok g st' m'
  | _ -> True

let wpre (g:CG.cgraph) (st:scope_table) (m:memo) (frames:list frame) : prop =
  CG.graph_inv g /\ scopes_ok st (CG.sort_count g) /\ memo_ok g st m /\ frames_below frames st.count

let step_ok (g:CG.cgraph) (st:scope_table) (r:stepped) : prop =
  match r with
  | Next st' m' _ _ frames' -> wpre g st' m' frames' /\ scopes_grow st st'
  | Stop r -> walk_ok g st r

let quant_bids_below (g:CG.cgraph) (x:nat) (ok:bool) (bids:list nat) (y r:nat)
  : Lemma (requires CG.graph_inv g /\ x < CG.node_count g /\ CG.node_of g x == Some (T.ENQuant ok bids y r))
          (ensures CS.all_below bids (CG.sort_count g))
  = CG.reveal_exact g x

let lemma_scopes_grow_refl (st:scope_table) : Lemma (scopes_grow st st) = ()

let lemma_visit_var (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s n i:nat) (rest:list frame)
  : Lemma (requires wpre g st m (Visit x s :: rest) /\ not (memo_has m x s) /\ x < CG.node_count g /\
                    CG.node_of g x == Some (T.ENVar n i))
          (ensures step_ok g st (visit_step g st m w store x s rest))
  = lemma_scopes_grow_refl st;
    match scope_nth st s n w with
    | Some (Some j, w1) ->
      if j = i then
        (match record m x s w1 store with
         | Some (m', _, _) -> lemma_var_record g st m x s n i w
         | None -> ())
    | _ -> ()

let lemma_visit_app (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s:nat) (ok:bool) (xs:list nat) (r:nat)
                    (rest:list frame)
  : Lemma (requires wpre g st m (Visit x s :: rest) /\ not (memo_has m x s) /\ x < CG.node_count g /\
                    CG.node_of g x == Some (T.ENApp ok xs r))
          (ensures step_ok g st (visit_step g st m w store x s rest))
  = lemma_scopes_grow_refl st;
    lemma_visits_below xs s (Close x s :: rest) st.count

let lemma_visit_quant (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s:nat) (ok:bool) (bids:list nat)
                      (y r:nat) (rest:list frame)
  : Lemma (requires wpre g st m (Visit x s :: rest) /\ not (memo_has m x s) /\ x < CG.node_count g /\
                    CG.node_of g x == Some (T.ENQuant ok bids y r))
          (ensures step_ok g st (visit_step g st m w store x s rest))
  = if not ok then ()
    else begin
      quant_bids_below g x ok bids y r;
      lemma_under st (CG.sort_count g) bids s w store;
      match under st bids s w store with
      | Pushed st' s' w' store' ->
        CG.lemma_cgrows_refl g;
        lemma_memo_grows g g st st' m;
        lemma_frames_widen rest st.count st'.count;
        assert (s < st.count /\ st.count <= st'.count /\ s' < st'.count);
        if store' < 2 then ()
        else begin
          let frames' = Visit y s' :: Close x s :: rest in
          assert (frames_below frames' st'.count);
          assert (visit_step g st m w store x s rest == Next st' m w' (store' - 2) frames');
          assert (wpre g st' m frames')
        end
      | _ -> ()
    end

let lemma_visit (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s:nat) (rest:list frame)
  : Lemma (requires wpre g st m (Visit x s :: rest)) (ensures step_ok g st (visit_step g st m w store x s rest))
  = lemma_scopes_grow_refl st;
    if memo_has m x s || x >= CG.node_count g then ()
    else match CG.node_of g x with
      | None -> ()
      | Some (T.ENVar n i) -> lemma_visit_var g st m w store x s n i rest
      | Some (T.ENApp ok xs r) -> lemma_visit_app g st m w store x s ok xs r rest
      | Some (T.ENQuant ok bids y r) -> lemma_visit_quant g st m w store x s ok bids y r rest

let lemma_close_app (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s:nat) (xs:list nat) (r:nat)
                    (rest:list frame)
  : Lemma (requires wpre g st m (Close x s :: rest) /\ x < CG.node_count g /\ CG.node_of g x == Some (T.ENApp true xs r))
          (ensures step_ok g st (close_step g st m w store x s rest))
  = lemma_scopes_grow_refl st;
    match all_recorded m xs s w with
    | Some (true, w1) ->
      (match record m x s w1 store with
       | Some (m', _, _) -> lemma_app_record g st m x s xs r w
       | None -> ())
    | _ -> ()

let lemma_close_quant_unfold (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s:nat) (rest:list frame)
                             (bids:list nat) (y r:nat)
  : Lemma (requires x < CG.node_count g /\ CG.node_of g x == Some (T.ENQuant true bids y r))
          (ensures close_step g st m w store x s rest ==
                   (match under st bids s w store with
                    | PushExhausted p -> Stop (WalkExhausted p)
                    | Pushed st' s' w1 store1 ->
                      if w1 < 2 * tu then Stop (WalkExhausted T.Validation)
                      else if not (memo_has m y s') then Stop WalkFailed
                      else (match record m x s (w1 - 2 * tu) store1 with
                            | Some (m', w2, s2) -> Next st' m' w2 s2 rest
                            | None -> stop_record (w1 - 2 * tu))))
  = ()

let lemma_close_quant (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s:nat) (bids:list nat) (y r:nat)
                      (rest:list frame)
  : Lemma (requires wpre g st m (Close x s :: rest) /\ x < CG.node_count g /\
                    CG.node_of g x == Some (T.ENQuant true bids y r))
          (ensures step_ok g st (close_step g st m w store x s rest))
  = lemma_close_quant_unfold g st m w store x s rest bids y r;
    assert (s < st.count /\ frames_below rest st.count);
    quant_bids_below g x true bids y r;
    lemma_under st (CG.sort_count g) bids s w store;
    match under st bids s w store with
    | Pushed st' s' w1 store1 ->
      if w1 < 2 * tu || not (memo_has m y s') then ()
      else
        (match record m x s (w1 - 2 * tu) store1 with
         | Some (m', w2, s2) ->
           CG.lemma_cgrows_refl g;
           lemma_memo_grows g g st st' m;
           lemma_quant_record g st st' m x s bids y r s';
           lemma_frames_widen rest st.count st'.count;
           assert (close_step g st m w store x s rest == Next st' m' w2 s2 rest);
           assert (memo_ok g st' m' /\ scopes_ok st' (CG.sort_count g) /\ frames_below rest st'.count);
           assert (wpre g st' m' rest)
         | None -> ())
    | _ -> ()

let lemma_close (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (x s:nat) (rest:list frame)
  : Lemma (requires wpre g st m (Close x s :: rest)) (ensures step_ok g st (close_step g st m w store x s rest))
  = if x >= CG.node_count g then ()
    else match CG.node_of g x with
      | Some (T.ENApp true xs r) -> lemma_close_app g st m w store x s xs r rest
      | Some (T.ENQuant true bids y r) -> lemma_close_quant g st m w store x s bids y r rest
      | _ -> ()

let lemma_walk_step (g:CG.cgraph) (st:scope_table) (m:memo) (w store:nat) (fr:frame) (rest:list frame)
  : Lemma (requires wpre g st m (fr :: rest)) (ensures step_ok g st (walk_step g st m w store fr rest))
  = match fr with
    | Visit x s -> lemma_visit g st m w store x s rest
    | Close x s -> lemma_close g st m w store x s rest

let lemma_walk_ok_trans (g:CG.cgraph) (st st':scope_table) (r:walked)
  : Lemma (requires scopes_grow st st' /\ walk_ok g st' r) (ensures walk_ok g st r)
  = ()

let rec lemma_walk (g:CG.cgraph) (st:scope_table) (m:memo) (work store:nat) (frames:list frame)
  : Lemma (requires wpre g st m frames) (ensures walk_ok g st (walk g st m work store frames)) (decreases work)
  = match frames with
    | [] -> lemma_scopes_grow_refl st
    | fr :: rest ->
      if work < 1 + 2 * tu then ()
      else begin
        lemma_walk_step g st m (work - (1 + 2 * tu)) store fr rest;
        match walk_step g st m (work - (1 + 2 * tu)) store fr rest with
        | Next st' m' w' s' frames' ->
          lemma_walk g st' m' w' s' frames';
          lemma_walk_ok_trans g st st' (walk g st' m' w' s' frames')
        | Stop _ -> ()
      end

(* A scope `ids` checked for the nodes `xs`: the walk, then each node looked up. *)
let lemma_recorded (g:CG.cgraph) (st:scope_table) (m:memo) (xs:list nat) (s w:nat)
  : Lemma (requires memo_ok g st m /\ (match all_recorded m xs s w with Some (true, _) -> True | _ -> False) /\
                    Some? (CG.values_of g xs))
          (ensures D.scoped_args (scope_sorts g st s) (Some?.v (CG.values_of g xs)) == true)
  = lemma_all_recorded g st m xs s w (Some?.v (CG.values_of g xs))

let lemma_scopes_widen (st:scope_table) (b b':nat)
  : Lemma (requires scopes_ok st b /\ b <= b') (ensures scopes_ok st b')
  = ()

let lemma_empty_scopes (b:nat) : Lemma (scopes_ok empty_scopes b) = ()
