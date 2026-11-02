(*
   Z3CheckedScope.fst

   The scope check of prepared expressions. `walk` checks nodes of a
   `Z3CheckedTerms` graph at scopes that are lists of checked sort ids (`Var
   0` first), within explicit Validation and Storage budgets. A variable's
   sort is compared with its binder's by checked id; an application and a
   quantifier contribute the scope-independent conditions computed during
   preparation; a quantifier's body is checked under its binders, reversed,
   in front of the scope.

   `lemma_walk`: a walk that finishes with `true` establishes
   `Z3Definitions.scoped_args` of every frame's expressions at the scope its
   ids denote, for every graph in which the frame's nodes `represent` them.
   Exhaustion and failure establish nothing; nothing is stored or reused.

   The walk keeps its pending work on an explicit worklist of frames and is a
   self tail call (a loop on the Cherry backend).

   Units, charged before the step they pay for. Validation: one per step,
   `table_units` per node read, `n + 1` to read the binder of `Var n`, and
   `2 m + 1` to count `m` binders and build the scope under them. Storage:
   one cell per frame pushed or replaced and `m + 1` cells for the scope
   under `m` binders and the body's list.
*)
module Z3CheckedScope

open Z3AstTheory
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module T = Z3CheckedTerms
module D = Z3Definitions

(* The scope ids, the scope's length and the nodes still to check there. *)
type walk_frame = list nat & nat & list nat

noeq
type walked =
  | Walked : ok:bool -> work:nat -> store:nat -> walked
  | WalkExhausted : phase:T.phase -> walked

let rec nth_id (sc:list nat) (n:nat) : Tot (option nat) (decreases sc) =
  match sc with
  | [] -> None
  | x :: rest -> if n = 0 then Some x else nth_id rest (n - 1)

(* The length of `l`, one unit per element; `None` beyond `work`. *)
let rec count_within (#a:Type) (work acc:nat) (l:list a)
  : Tot (r:option (nat & nat){Some? r ==> snd (Some?.v r) <= work}) (decreases l) =
  match l with
  | [] -> Some (acc, work)
  | _ :: rest -> if work = 0 then None else count_within (work - 1) (acc + 1) rest

(* `L.rev bs @ sc`, by a self tail call. *)
let rec under (bs sc:list nat) : Tot (list nat) (decreases bs) =
  match bs with
  | [] -> sc
  | b :: rest -> under rest (b :: sc)

let rec walk (g:T.term_graph) (work store:nat) (frames:list walk_frame)
  : Tot walked (decreases work) =
  match frames with
  | [] -> Walked true work store
  | (sc, len, xs) :: rest ->
    if work = 0 then WalkExhausted T.Validation
    else
      let w = work - 1 in
      match xs with
      | [] -> walk g w store rest
      | x :: xs' ->
        if w < CS.table_units then WalkExhausted T.Validation
        else if store = 0 then WalkExhausted T.Storage
        else
          let w1 = w - CS.table_units in
          let s1 = store - 1 in
          let rest' = (sc, len, xs') :: rest in
          match T.expr_node g x with
          | None -> Walked false w1 s1
          | Some (T.ENVar n i) ->
            if n >= len then Walked false w1 s1
            else if w1 < n + 1 then WalkExhausted T.Validation
            else
              (match nth_id sc n with
               | Some j -> if j = i then walk g (w1 - (n + 1)) s1 rest' else Walked false (w1 - (n + 1)) s1
               | None -> Walked false (w1 - (n + 1)) s1)
          | Some (T.ENApp ok ys _) ->
            if not ok then Walked false w1 s1
            else if s1 = 0 then WalkExhausted T.Storage
            else walk g w1 (s1 - 1) ((sc, len, ys) :: rest')
          | Some (T.ENQuant ok bids y _) ->
            if not ok then Walked false w1 s1
            else
              (match count_within w1 0 bids with
               | None -> WalkExhausted T.Validation
               | Some (m, w2) ->
                 if w2 < m + 1 then WalkExhausted T.Validation
                 else if s1 < m + 1 then WalkExhausted T.Storage
                 else walk g (w2 - (m + 1)) (s1 - (m + 1)) ((under bids sc, m + len, [y]) :: rest'))

(* --- What a successful walk earns ------------------------------------------------------- *)

let rec lemma_count_within (#a:Type) (work acc:nat) (l:list a)
  : Lemma (ensures (match count_within work acc l with
                    | Some (m, _) -> m == acc + L.length l
                    | None -> True))
          (decreases l)
  = match l with [] -> () | _ :: rest -> if work > 0 then lemma_count_within (work - 1) (acc + 1) rest

let rec lemma_under (bs sc:list nat) : Lemma (ensures under bs sc == L.append (L.rev bs) sc) (decreases bs) =
  match bs with
  | [] -> ()
  | b :: rest ->
    lemma_under rest (b :: sc);
    Z3List.lemma_rev_cons b rest;
    L.append_assoc (L.rev rest) [b] sc

let rec lemma_map_rev (#a #b:Type) (f:a -> b) (l:list a)
  : Lemma (ensures L.map f (L.rev l) == L.rev (L.map f l)) (decreases l)
  = match l with
    | [] -> ()
    | x :: rest ->
      lemma_map_rev f rest;
      Z3List.lemma_rev_cons x rest;
      Z3List.lemma_rev_cons (f x) (L.map f rest);
      FStar.List.Tot.Properties.map_append f (L.rev rest) [x]

let rec lemma_nth_id (f:nat -> sort) (sc:list nat) (n:nat)
  : Lemma (ensures (match nth_id sc n with
                    | Some j -> n < L.length sc /\ n < L.length (L.map f sc) /\ L.index (L.map f sc) n == f j
                    | None -> n >= L.length sc))
          (decreases sc)
  = match sc with
    | [] -> ()
    | _ :: rest -> if n > 0 then lemma_nth_id f rest (n - 1)

let lemma_scope_under (t:CS.sort_table) (bids sc:list nat)
  : Lemma (L.map (T.interp t) (under bids sc) == L.append (L.rev (L.map (T.interp t) bids)) (L.map (T.interp t) sc) /\
           L.length (under bids sc) == L.length bids + L.length sc /\
           CS.all_below (under bids sc) t.CS.node_count ==
             (CS.all_below bids t.CS.node_count && CS.all_below sc t.CS.node_count))
  = lemma_under bids sc;
    FStar.List.Tot.Properties.map_append (T.interp t) (L.rev bids) sc;
    lemma_map_rev (T.interp t) bids;
    FStar.List.Tot.Properties.append_length (L.rev bids) sc;
    FStar.List.Tot.Properties.rev_length bids;
    T.lemma_all_below_append (L.rev bids) sc t.CS.node_count;
    T.lemma_all_below_rev bids t.CS.node_count

(* The frames' nodes represent the expression lists `es`, at scopes of valid ids. *)
noextract
let rec frames_rel (g:T.term_graph) (frames:list walk_frame) (es:list (list expr))
  : Tot prop (decreases frames) =
  match frames, es with
  | [], [] -> True
  | (sc, len, xs) :: rest, a :: es' ->
    len == L.length sc /\ CS.all_below sc g.T.sorts.CS.node_count /\ T.represents_list g xs a /\
    frames_rel g rest es'
  | _, _ -> False

noextract
let rec frames_hold (g:T.term_graph) (frames:list walk_frame) (es:list (list expr))
  : Tot prop (decreases frames) =
  match frames, es with
  | [], [] -> True
  | (sc, _, _) :: rest, a :: es' -> D.scoped_args (L.map (T.interp g.T.sorts) sc) a == true /\ frames_hold g rest es'
  | _, _ -> False

let walk_true (r:walked) : bool = match r with Walked ok _ _ -> ok | WalkExhausted _ -> false

let lemma_walk_var (g:T.term_graph) (sc:list nat) (n:nat) (s:sort) (i j:nat)
  : Lemma (requires nth_id sc n == Some j /\ j = i /\ T.interp g.T.sorts i == s)
          (ensures D.scoped (L.map (T.interp g.T.sorts) sc) (Var n s) == true)
  = lemma_nth_id (T.interp g.T.sorts) sc n;
    FStar.List.Tot.Properties.map_lemma (T.interp g.T.sorts) sc

let rec lemma_walk (g:T.term_graph) (work store:nat) (frames:list walk_frame) (es:list (list expr))
  : Lemma (requires frames_rel g frames es /\ walk_true (walk g work store frames))
          (ensures frames_hold g frames es)
          (decreases work)
  = match frames, es with
    | [], [] -> ()
    | (sc, len, xs) :: rest, a :: es' ->
      let w = work - 1 in
      (match xs, a with
       | [], [] -> lemma_walk g w store rest es'
       | x :: xs', e :: a' ->
         let w1 = w - CS.table_units in
         let s1 = store - 1 in
         let rest' = (sc, len, xs') :: rest in
         let f = T.interp g.T.sorts in
         (match e, T.expr_node g x with
          | Var n s, Some (T.ENVar _ i) ->
            lemma_walk g (w1 - (n + 1)) s1 rest' (a' :: es');
            lemma_walk_var g sc n s i (Some?.v (nth_id sc n))
          | App fd args, Some (T.ENApp _ ys _) ->
            lemma_walk g w1 (s1 - 1) ((sc, len, ys) :: rest') (args :: a' :: es')
          | Quantifier k bs q b, Some (T.ENQuant _ bids y _) ->
            lemma_count_within w1 0 bids;
            let m, w2 = Some?.v (count_within w1 0 bids) in
            lemma_scope_under g.T.sorts bids sc;
            lemma_walk g (w2 - (m + 1)) (s1 - (m + 1)) ((under bids sc, m + len, [y]) :: rest') ([b] :: a' :: es')
          | _, _ -> ())
       | _, _ -> ())
    | _, _ -> ()

(* One expression list at one scope. *)
let check_scoped (g:T.term_graph) (sc:list nat) (len:nat) (xs:list nat) (work store:nat) : walked =
  walk g work store [(sc, len, xs)]

let lemma_check_scoped (g:T.term_graph) (sc:list nat) (len:nat) (xs:list nat) (work store:nat) (es:list expr)
  : Lemma (requires len == L.length sc /\ CS.all_below sc g.T.sorts.CS.node_count /\ T.represents_list g xs es /\
                    walk_true (check_scoped g sc len xs work store))
          (ensures D.scoped_args (L.map (T.interp g.T.sorts) sc) es == true)
  = lemma_walk g work store [(sc, len, xs)] [es]
