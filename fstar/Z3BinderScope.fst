(*
   Z3BinderScope.fst

   Structural theorems about the scope guard of binder certificates
   (`Z3UnifiedProof.binder_scoped`), with no semantic model.

   A certificate's entries are judgments at different binder depths. The
   guard assigns every entry the scopes at which the root uses it, starting
   from the root at the closed top-level scope `[]`, and checks every entry's
   judgment at each of its scopes, within explicit resource bounds.

   * Specification. `entries_scoped` states the forward check without work
     accounting: every assigned scope of every entry scopes its judgment
     (`binder_judgment_scoped`, i.e. `Z3Definitions.scoped` of each side),
     and every premise is an earlier entry assigned the premise scope
     (`premise_scope_of`: `L.rev bs @ s` under binder sorts `bs`, else `s`).
     `lemma_entries_checked` proves that the bounded executable check implies
     it: the work-counted primitives compute exactly the list length, scope
     membership and `Z3Definitions.scoped` whenever they finish. The guard
     builds the scope under binders with the loop `scope_under`, which is
     `L.rev_acc` and `L.rev bs @ s` (`lemma_scope_under`), and walks
     expressions and compares sorts over explicit worklists. The recursive
     definitions of 0ebb92579 are kept for the proof only (`*_rec`,
     `binder_premise_scope_append`), and the loops change no result and no
     remaining work (`lemma_sort_same`, `lemma_sort_list_same`,
     `lemma_scoped_same`, `lemma_scoped_args_same`,
     `lemma_premise_scope_same`).
   * Theorem 1, `lemma_root_scoped` / `lemma_checked_root_scoped`: the root is
     an entry, it is assigned `[]`, and its judgment (the node conclusion) is
     scoped at `[]` (closed and well sorted).
   * Theorem 2, `lemma_edge_scoped`: for every entry `k`, every scope `s`
     assigned to it and every premise `p` of it, `k`'s judgment is scoped at
     `s`, `p` is an earlier entry (`0 <= p < k`), `p` was assigned the scope
     `premise_scope_of k s`, and `p`'s judgment is scoped there. A shared entry
     is checked at every scope it is assigned.
   * `lemma_checked_guard`: `check_binder_with_context` accepts only when
     `check_binder_entries` builds a cache holding the conclusion at the root
     and the guard holds on that cache with the checker's bounds; the
     theorems then apply to the checker's own cache.

   These are facts about the guard's decision only. They do not make any
   rule's step semantically sound; `Z3BinderKernel` proves that for a
   fragment of entry kinds.
*)
module Z3BinderScope

open Z3AstTheory
open Z3UnifiedProof
module I = Z3ProofIndex
module D = Z3Definitions
module DV = Z3DatatypeValue
module SK = Z3Skolemization
module L = FStar.List.Tot

(* --- Specification ------------------------------------------------------------ *)

let binder_judgment_scoped (scope:list sort) (j:judgment) : bool =
  match j with
  | Holds e -> D.scoped scope e
  | Equal a b | Observational a b -> D.scoped scope a && D.scoped scope b

(* The scope of the premises of an entry used at `s`. *)
let premise_scope_of (e:binder_entry) (s:list sort) : list sort =
  match e.binder_sorts with
  | Some bs -> L.append (L.rev bs) s
  | None -> s

let rec premises_demanded (t:scope_demands) (k:int) (ps:list int) (scope:list sort)
  : Tot bool (decreases ps) =
  match ps with
  | [] -> true
  | p :: rest -> 0 <= p && p < k && L.mem scope (scope_demanded t p) && premises_demanded t k rest scope

let rec entry_scoped (t:scope_demands) (k:int) (e:binder_entry) (j:judgment) (scopes:list (list sort))
  : Tot bool (decreases scopes) =
  match scopes with
  | [] -> true
  | s :: rest ->
    binder_judgment_scoped s j && premises_demanded t k e.binder_premises (premise_scope_of e s) &&
    entry_scoped t k e j rest

let rec entries_scoped (t:scope_demands) (cache:I.index_tree judgment) (k:nat) (entries:list binder_entry)
  : Tot bool (decreases entries) =
  match entries with
  | [] -> true
  | e :: rest ->
    (match I.index_find cache k with
     | Some j -> entry_scoped t k e j (scope_demanded t k)
     | None -> false) &&
    entries_scoped t cache (k + 1) rest

(* --- The bounded primitives compute the specification -------------------------- *)

(* The scope-length loop: `acc` plus the length and the work left, or `None`
   when the list is longer than the work. *)
let rec lemma_length_acc (#a:Type) (work acc:nat) (l:list a)
  : Lemma (ensures scope_length_acc work acc l ==
                   (if L.length l <= work then Some (acc + L.length l, work - L.length l) else None))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: rest -> if work > 0 then lemma_length_acc (work - 1) (acc + 1) rest

(* The recursive definition of d50187500, as deep as the list on the Cherry
   backend, computes the same: the loop changes no result or charge. *)
let rec scope_length_rec (#a:Type) (work:nat) (l:list a)
  : Tot (option (nat & nat)) (decreases l) =
  match l with
  | [] -> Some (0, work)
  | _ :: rest ->
    if work = 0 then None
    else (match scope_length_rec (work - 1) rest with
          | Some (n, w) -> Some (n + 1, w)
          | None -> None)

let rec lemma_length_rec (#a:Type) (work:nat) (l:list a)
  : Lemma (ensures scope_length_rec work l ==
                   (if L.length l <= work then Some (L.length l, work - L.length l) else None))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: rest -> if work > 0 then lemma_length_rec (work - 1) rest

let lemma_length_same (#a:Type) (work:nat) (l:list a)
  : Lemma (scope_length_within work l == scope_length_rec work l)
  = lemma_length_acc work 0 l; lemma_length_rec work l

let lemma_length_within (#a:Type) (work:nat) (l:list a)
  : Lemma (requires Some? (scope_length_within work l))
          (ensures fst (Some?.v (scope_length_within work l)) == L.length l)
  = lemma_length_acc work 0 l

let rec lemma_count_cells (#a:Type) (acc:nat) (l:list a)
  : Lemma (ensures count_cells acc l == acc + L.length l) (decreases l)
  = match l with
    | [] -> ()
    | _ :: rest -> lemma_count_cells (acc + 1) rest

(* The guard charges a name `FStar.String.strlen` units, counted without
   `List.Tot.length`'s recursion. *)
let lemma_name_length (s:string) : Lemma (name_length s == FStar.String.strlen s)
  = lemma_count_cells 0 (FStar.String.list_of_string s)

(* The recursive sort comparison of d50187500/0ebb92579, word for word under
   new names, proof only: as deep as the sorts on the Cherry backend. *)
let rec sort_eq_within_rec (work:nat) (s t:sort) : Tot (option (bool & nat)) (decreases s) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    (match s, t with
     | BaseSort a, BaseSort b ->
       (match scope_charge w (name_length a + name_length b) with
        | Some w' -> Some (a = b, w')
        | None -> None)
     | ArraySort d1 r1, ArraySort d2 r2 ->
       (match sort_list_eq_within_rec w d1 d2 with
        | Some (true, w') -> sort_eq_within_rec w' r1 r2
        | r -> r)
     | _, _ -> Some (false, w))

and sort_list_eq_within_rec (work:nat) (l1 l2:list sort) : Tot (option (bool & nat)) (decreases l1) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    (match l1, l2 with
     | [], [] -> Some (true, w)
     | a :: l1', b :: l2' ->
       (match sort_eq_within_rec w a b with
        | Some (true, w') -> sort_list_eq_within_rec w' l1' l2'
        | r -> r)
     | _, _ -> Some (false, w))

(* What the worklist means: the recursive comparisons of its tasks in order,
   up to the first that is not `Some (true, _)`. *)
let rec sort_tasks_spec (work:nat) (tasks:list sort_task) : Tot (option (bool & nat)) (decreases tasks) =
  match tasks with
  | [] -> Some (true, work)
  | SortPair s t :: rest ->
    (match sort_eq_within_rec work s t with
     | Some (true, w) -> sort_tasks_spec w rest
     | r -> r)
  | SortListPair l1 l2 :: rest ->
    (match sort_list_eq_within_rec work l1 l2 with
     | Some (true, w) -> sort_tasks_spec w rest
     | r -> r)

let rec lemma_sort_tasks (work:nat) (tasks:list sort_task)
  : Lemma (ensures sort_tasks_within work tasks == sort_tasks_spec work tasks) (decreases work)
  = match tasks with
    | [] -> ()
    | SortPair s t :: rest ->
      (match scope_charge work 1 with
       | None -> ()
       | Some w ->
         (match s, t with
          | BaseSort a, BaseSort b ->
            (match scope_charge w (name_length a + name_length b) with
             | Some w' -> if a = b then lemma_sort_tasks w' rest
             | None -> ())
          | ArraySort d1 r1, ArraySort d2 r2 ->
            lemma_sort_tasks w (SortListPair d1 d2 :: SortPair r1 r2 :: rest);
            (match sort_list_eq_within_rec w d1 d2 with
             | Some (true, w') -> ()
             | _ -> ())
          | _, _ -> ()))
    | SortListPair l1 l2 :: rest ->
      (match scope_charge work 1 with
       | None -> ()
       | Some w ->
         (match l1, l2 with
          | [], [] -> lemma_sort_tasks w rest
          | a :: l1', b :: l2' ->
            lemma_sort_tasks w (SortPair a b :: SortListPair l1' l2' :: rest);
            (match sort_eq_within_rec w a b with
             | Some (true, w') -> ()
             | _ -> ())
          | _, _ -> ()))

(* The worklist comparison changes no result and no remaining work. *)
let lemma_sort_same (work:nat) (s t:sort)
  : Lemma (sort_eq_within work s t == sort_eq_within_rec work s t)
  = lemma_sort_tasks work [SortPair s t]

let lemma_sort_list_same (work:nat) (l1 l2:list sort)
  : Lemma (sort_list_eq_within work l1 l2 == sort_list_eq_within_rec work l1 l2)
  = lemma_sort_tasks work [SortListPair l1 l2]

let rec lemma_sort_eq_within_rec (work:nat) (s t:sort)
  : Lemma (requires Some? (sort_eq_within_rec work s t))
          (ensures fst (Some?.v (sort_eq_within_rec work s t)) == sort_eq s t)
          (decreases s)
  = let w = work - 1 in
    match s, t with
    | ArraySort d1 r1, ArraySort d2 r2 ->
      lemma_sort_list_eq_within_rec w d1 d2;
      (match sort_list_eq_within_rec w d1 d2 with
       | Some (true, w') -> lemma_sort_eq_within_rec w' r1 r2
       | _ -> ())
    | _, _ -> ()

and lemma_sort_list_eq_within_rec (work:nat) (l1 l2:list sort)
  : Lemma (requires Some? (sort_list_eq_within_rec work l1 l2))
          (ensures fst (Some?.v (sort_list_eq_within_rec work l1 l2)) == sort_list_eq l1 l2)
          (decreases l1)
  = let w = work - 1 in
    match l1, l2 with
    | a :: l1', b :: l2' ->
      lemma_sort_eq_within_rec w a b;
      (match sort_eq_within_rec w a b with
       | Some (true, w') -> lemma_sort_list_eq_within_rec w' l1' l2'
       | _ -> ())
    | _, _ -> ()

let lemma_sort_eq_within (work:nat) (s t:sort)
  : Lemma (requires Some? (sort_eq_within work s t))
          (ensures fst (Some?.v (sort_eq_within work s t)) == sort_eq s t)
  = lemma_sort_same work s t;
    lemma_sort_eq_within_rec work s t

let lemma_sort_list_eq_within (work:nat) (l1 l2:list sort)
  : Lemma (requires Some? (sort_list_eq_within work l1 l2))
          (ensures fst (Some?.v (sort_list_eq_within work l1 l2)) == sort_list_eq l1 l2)
  = lemma_sort_list_same work l1 l2;
    lemma_sort_list_eq_within_rec work l1 l2

(* The same as structural equality. *)
let lemma_sort_equal_within (work:nat) (s t:sort)
  : Lemma (requires Some? (sort_eq_within work s t))
          (ensures fst (Some?.v (sort_eq_within work s t)) == (s = t))
  = lemma_sort_eq_within work s t;
    DV.lemma_sort_eq s t

let rec lemma_sorts_match_within (work:nat) (args:list expr) (dom:list sort)
  : Lemma (requires Some? (sorts_match_within work args dom))
          (ensures fst (Some?.v (sorts_match_within work args dom)) == sorts_match args dom)
          (decreases args)
  = let w = work - 1 in
    match args, dom with
    | a :: args', d :: dom' ->
      lemma_sort_eq_within w (get_sort a) d;
      (match sort_eq_within w (get_sort a) d with
       | Some (true, w') -> lemma_sorts_match_within w' args' dom'
       | _ -> ())
    | _, _ -> ()

let rec lemma_mem_within (work:nat) (scope:list sort) (scopes:list (list sort))
  : Lemma (requires Some? (scope_mem_within work scope scopes))
          (ensures fst (Some?.v (scope_mem_within work scope scopes)) == L.mem scope scopes)
          (decreases scopes)
  = match scopes with
    | [] -> ()
    | x :: rest ->
      lemma_sort_list_eq_within work x scope;
      DV.lemma_sort_list_eq x scope;
      (match sort_list_eq_within work x scope with
       | Some (false, w) -> lemma_mem_within w scope rest
       | _ -> ())

let rec lemma_nth (scope:list sort) (n:nat)
  : Lemma (requires n < L.length scope)
          (ensures scope_nth scope n == Some (L.index scope n))
          (decreases scope)
  = match scope with
    | _ :: rest -> if n = 0 then () else lemma_nth rest (n - 1)

let lemma_binder_scope_length (bs scope:list sort)
  : Lemma (L.length (L.append (L.rev bs) scope) == L.length bs + L.length scope)
  = FStar.List.Tot.Properties.append_length (L.rev bs) scope;
    FStar.List.Tot.Properties.rev_length bs

(* The guard's scope under binders: `scope_under` is the library's
   tail-recursive `L.rev_acc`, which is `L.rev bs @ scope`. *)
let rec lemma_scope_under_rev_acc (bs scope:list sort)
  : Lemma (ensures scope_under bs scope == L.rev_acc bs scope) (decreases bs)
  = match bs with
    | [] -> ()
    | b :: rest -> lemma_scope_under_rev_acc rest (b :: scope)

let lemma_rev_acc_scope (#a:Type) (bs scope:list a)
  : Lemma (L.rev_acc bs scope == L.append (L.rev bs) scope)
  = FStar.List.Tot.Properties.rev_acc_rev' bs scope;
    FStar.List.Tot.Properties.rev_rev' bs

let lemma_scope_under (bs scope:list sort)
  : Lemma (scope_under bs scope == L.append (L.rev bs) scope)
  = lemma_scope_under_rev_acc bs scope;
    lemma_rev_acc_scope bs scope

(* The recursive walk of d50187500/0ebb92579, word for word under new names,
   proof only: it built the scope under binders with `L.append (L.rev bs)
   scope` and recursed through arguments and bodies, as deep as the
   expression and as long as `bs` on the Cherry backend. With
   `sort_eq_within == sort_eq_within_rec` (`lemma_sort_same`) and the
   unchanged `sorts_match_within`, it is the 0ebb92579 function. *)
let rec scoped_within_rec (work:nat) (scope:list sort) (len:nat) (e:expr)
  : Tot (option (bool & nat)) (decreases e) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    (match e with
     | Var n s ->
       if n < len then
         (match scope_charge w (n + 1) with
          | Some w' ->
            (match scope_nth scope n with
             | Some s' -> sort_eq_within w' s' s
             | None -> Some (false, w'))
          | None -> None)
       else Some (false, w)
     | App f args ->
       (match sorts_match_within w args f.domain with
        | Some (true, w') -> scoped_args_within_rec w' scope len args
        | r -> r)
     | Quantifier k bs s b ->
       (match scope_length_within w bs with
        | Some (m, w1) ->
          (match scope_charge w1 (2 * m + 1) with
           | Some w2 ->
             (match sort_eq_within w2 s (quant_sort k bs (get_sort b)) with
              | Some (true, w3) ->
                (match (if k = Lambda_k then Some (true, w3) else sort_eq_within w3 (get_sort b) bool_sort) with
                 | Some (true, w4) -> scoped_within_rec w4 (L.append (L.rev bs) scope) (m + len) b
                 | r -> r)
              | r -> r)
           | None -> None)
        | None -> None))

and scoped_args_within_rec (work:nat) (scope:list sort) (len:nat) (args:list expr)
  : Tot (option (bool & nat)) (decreases args) =
  match args with
  | [] -> Some (true, work)
  | a :: rest ->
    (match scoped_within_rec work scope len a with
     | Some (true, w) -> scoped_args_within_rec w scope len rest
     | Some (false, w) -> Some (false, w)
     | None -> None)

(* The premise scope of 0ebb92579, proof only. *)
let binder_premise_scope_append (work:nat) (e:binder_entry) (scope:list sort) (len:nat)
  : option (list sort & nat & nat) =
  match e.binder_sorts with
  | None -> Some (scope, len, work)
  | Some bs ->
    (match scope_length_within work bs with
     | Some (m, w) ->
       if m + len > binder_scope_limit then None
       else (match scope_charge w (2 * m + 1) with
             | Some w' -> Some (L.append (L.rev bs) scope, m + len, w')
             | None -> None)
     | None -> None)

(* What the worklist of frames means: the recursive walk of every frame in
   order, up to the first that is not `Some (true, _)`. *)
let rec scoped_frames_spec (work:nat) (frames:list scope_frame)
  : Tot (option (bool & nat)) (decreases frames) =
  match frames with
  | [] -> Some (true, work)
  | (scope, len, es) :: rest ->
    (match scoped_args_within_rec work scope len es with
     | Some (true, w) -> scoped_frames_spec w rest
     | r -> r)

let rec lemma_scoped_frames (work:nat) (frames:list scope_frame)
  : Lemma (ensures scoped_frames_within work frames == scoped_frames_spec work frames)
          (decreases %[frame_nodes frames; L.length frames])
  = match frames with
    | [] -> ()
    | (_, _, []) :: rest -> lemma_scoped_frames work rest
    | (scope, len, e :: es) :: rest ->
      let rest' = (scope, len, es) :: rest in
      (match scope_charge work 1 with
       | None -> ()
       | Some w ->
         (match e with
          | Var n s ->
            if n < len then
              (match scope_charge w (n + 1) with
               | Some w' ->
                 (match scope_nth scope n with
                  | Some s' ->
                    (match sort_eq_within w' s' s with
                     | Some (true, w'') -> lemma_scoped_frames w'' rest'
                     | _ -> ())
                  | None -> ())
               | None -> ())
          | App f args ->
            (match sorts_match_within w args f.domain with
             | Some (true, w') ->
               lemma_scoped_frames w' ((scope, len, args) :: rest');
               (match scoped_args_within_rec w' scope len args with
                | Some (true, w'') -> ()
                | _ -> ())
             | _ -> ())
          | Quantifier k bs s b ->
            lemma_scope_under bs scope;
            (match scope_length_within w bs with
             | Some (m, w1) ->
               (match scope_charge w1 (2 * m + 1) with
                | Some w2 ->
                  (match sort_eq_within w2 s (quant_sort k bs (get_sort b)) with
                   | Some (true, w3) ->
                     (match (if k = Lambda_k then Some (true, w3) else sort_eq_within w3 (get_sort b) bool_sort) with
                      | Some (true, w4) ->
                        lemma_scoped_frames w4 ((scope_under bs scope, m + len, [b]) :: rest');
                        (match scoped_within_rec w4 (scope_under bs scope) (m + len) b with
                         | Some (true, w'') -> ()
                         | _ -> ())
                      | _ -> ())
                   | _ -> ())
                | None -> ())
             | None -> ())))

(* The worklist walk changes no result and no remaining work. *)
let lemma_scoped_same (work:nat) (scope:list sort) (len:nat) (e:expr)
  : Lemma (scoped_within work scope len e == scoped_within_rec work scope len e)
  = lemma_scoped_frames work [(scope, len, [e])];
    match scoped_within_rec work scope len e with
    | Some (true, w) -> ()
    | _ -> ()

let lemma_scoped_args_same (work:nat) (scope:list sort) (len:nat) (args:list expr)
  : Lemma (scoped_args_within work scope len args == scoped_args_within_rec work scope len args)
  = lemma_scoped_frames work [(scope, len, args)];
    match scoped_args_within_rec work scope len args with
    | Some (true, w) -> ()
    | _ -> ()

let lemma_premise_scope_same (work:nat) (e:binder_entry) (scope:list sort) (len:nat)
  : Lemma (binder_premise_scope_within work e scope len == binder_premise_scope_append work e scope len)
  = match e.binder_sorts with
    | None -> ()
    | Some bs -> lemma_scope_under bs scope

let rec lemma_scoped_within_rec (work:nat) (scope:list sort) (len:nat) (e:expr)
  : Lemma (requires len == L.length scope /\ Some? (scoped_within_rec work scope len e))
          (ensures fst (Some?.v (scoped_within_rec work scope len e)) == D.scoped scope e)
          (decreases e)
  = let w = work - 1 in
    match e with
    | Var n s ->
      if n < len then (
        lemma_nth scope n;
        lemma_sort_equal_within (w - (n + 1)) (L.index scope n) s)
    | App f args ->
      lemma_sorts_match_within w args f.domain;
      (match sorts_match_within w args f.domain with
       | Some (true, w') -> lemma_scoped_args_within_rec w' scope len args
       | _ -> ())
    | Quantifier k bs s b ->
      let m, w1 = Some?.v (scope_length_within w bs) in
      lemma_length_within w bs;
      lemma_binder_scope_length bs scope;
      let w2 = w1 - (2 * m + 1) in
      lemma_sort_equal_within w2 s (quant_sort k bs (get_sort b));
      (match sort_eq_within w2 s (quant_sort k bs (get_sort b)) with
       | Some (true, w3) ->
         if k = Lambda_k then lemma_scoped_within_rec w3 (L.append (L.rev bs) scope) (m + len) b
         else (
           lemma_sort_equal_within w3 (get_sort b) bool_sort;
           match sort_eq_within w3 (get_sort b) bool_sort with
           | Some (true, w4) -> lemma_scoped_within_rec w4 (L.append (L.rev bs) scope) (m + len) b
           | _ -> ())
       | _ -> ())

and lemma_scoped_args_within_rec (work:nat) (scope:list sort) (len:nat) (args:list expr)
  : Lemma (requires len == L.length scope /\ Some? (scoped_args_within_rec work scope len args))
          (ensures fst (Some?.v (scoped_args_within_rec work scope len args)) == D.scoped_args scope args)
          (decreases args)
  = match args with
    | [] -> ()
    | a :: rest ->
      lemma_scoped_within_rec work scope len a;
      (match scoped_within_rec work scope len a with
       | Some (true, w) -> lemma_scoped_args_within_rec w scope len rest
       | _ -> ())

let lemma_scoped_within (work:nat) (scope:list sort) (len:nat) (e:expr)
  : Lemma (requires len == L.length scope /\ Some? (scoped_within work scope len e))
          (ensures fst (Some?.v (scoped_within work scope len e)) == D.scoped scope e)
  = lemma_scoped_same work scope len e;
    lemma_scoped_within_rec work scope len e

let lemma_scoped_args_within (work:nat) (scope:list sort) (len:nat) (args:list expr)
  : Lemma (requires len == L.length scope /\ Some? (scoped_args_within work scope len args))
          (ensures fst (Some?.v (scoped_args_within work scope len args)) == D.scoped_args scope args)
  = lemma_scoped_args_same work scope len args;
    lemma_scoped_args_within_rec work scope len args

let lemma_judgment_scoped_within (work:nat) (scope:list sort) (len:nat) (j:judgment)
  : Lemma (requires len == L.length scope /\ Some? (judgment_scoped_within work scope len j) /\
                    fst (Some?.v (judgment_scoped_within work scope len j)) == true)
          (ensures binder_judgment_scoped scope j)
  = match j with
    | Holds e -> lemma_scoped_within work scope len e
    | Equal a b | Observational a b ->
      lemma_scoped_within work scope len a;
      (match scoped_within work scope len a with
       | Some (true, w) -> lemma_scoped_within w scope len b
       | _ -> ())

let lemma_premise_scope_within (work:nat) (e:binder_entry) (scope:list sort) (len:nat)
  : Lemma (requires len == L.length scope /\ Some? (binder_premise_scope_within work e scope len))
          (ensures (let (s', len', _) = Some?.v (binder_premise_scope_within work e scope len) in
                    s' == premise_scope_of e scope /\ len' == L.length s'))
  = match e.binder_sorts with
    | None -> ()
    | Some bs -> lemma_length_within work bs; lemma_binder_scope_length bs scope; lemma_scope_under bs scope

let rec lemma_premises_within (t:scope_demands) (k:int) (ps:list int) (scope:list sort) (work:nat)
  : Lemma (requires Some? (scope_premises_demanded t k ps scope work))
          (ensures premises_demanded t k ps scope)
          (decreases ps)
  = match ps with
    | [] -> ()
    | p :: rest ->
      let w = work - 1 in
      lemma_mem_within w scope (scope_demanded t p);
      (match scope_mem_within w scope (scope_demanded t p) with
       | Some (true, w') -> lemma_premises_within t k rest scope w'
       | _ -> ())

let rec lemma_entry_checked (t:scope_demands) (k:int) (e:binder_entry) (j:judgment)
                            (scopes:list (list sort)) (work:nat)
  : Lemma (requires Some? (scope_entry_checked t k e j scopes work))
          (ensures entry_scoped t k e j scopes)
          (decreases scopes)
  = match scopes with
    | [] -> ()
    | s :: rest ->
      let len, w = Some?.v (scope_length_within work s) in
      lemma_length_within work s;
      let w1 = snd (Some?.v (judgment_scoped_within w s len j)) in
      lemma_judgment_scoped_within w s len j;
      let s', _, w2 = Some?.v (binder_premise_scope_within w1 e s len) in
      lemma_premise_scope_within w1 e s len;
      lemma_premises_within t k e.binder_premises s' w2;
      lemma_entry_checked t k e j rest (Some?.v (scope_premises_demanded t k e.binder_premises s' w2))

let rec lemma_entries_checked (t:scope_demands) (cache:I.index_tree judgment) (k:nat)
                              (entries:list binder_entry) (work:nat)
  : Lemma (requires Some? (scope_entries_checked t cache k entries work))
          (ensures entries_scoped t cache k entries)
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      let w = work - 1 in
      let j = Some?.v (I.index_find cache k) in
      lemma_entry_checked t k e j (scope_demanded t k) w;
      lemma_entries_checked t cache (k + 1) rest
        (Some?.v (scope_entry_checked t k e j (scope_demanded t k) w))

(* --- Reading the specification -------------------------------------------------- *)

let rec lemma_premises_demanded (t:scope_demands) (k:int) (ps:list int) (scope:list sort) (p:int)
  : Lemma (requires premises_demanded t k ps scope /\ L.memP p ps)
          (ensures 0 <= p /\ p < k /\ L.memP scope (scope_demanded t p))
          (decreases ps)
  = match ps with
    | q :: rest ->
      if q = p then FStar.List.Tot.Properties.mem_memP scope (scope_demanded t p)
      else lemma_premises_demanded t k rest scope p

let rec lemma_entry_scoped (t:scope_demands) (k:int) (e:binder_entry) (j:judgment)
                           (scopes:list (list sort)) (s:list sort)
  : Lemma (requires entry_scoped t k e j scopes /\ L.memP s scopes)
          (ensures binder_judgment_scoped s j /\ premises_demanded t k e.binder_premises (premise_scope_of e s))
          (decreases scopes)
  = match scopes with
    | x :: rest -> if x = s then () else lemma_entry_scoped t k e j rest s

let rec lemma_entries_scoped (t:scope_demands) (cache:I.index_tree judgment) (k:nat)
                             (entries:list binder_entry) (i:nat)
  : Lemma (requires entries_scoped t cache k entries /\ i < L.length entries)
          (ensures Some? (I.index_find cache (k + i)) /\
                   entry_scoped t (k + i) (L.index entries i) (Some?.v (I.index_find cache (k + i)))
                     (scope_demanded t (k + i)))
          (decreases entries)
  = match entries with
    | _ :: rest -> if i = 0 then () else lemma_entries_scoped t cache (k + 1) rest (i - 1)

(* What the specification gives for one entry and one of its scopes. *)
let lemma_scoped_at (t:scope_demands) (cache:I.index_tree judgment) (entries:list binder_entry)
                    (k:nat) (s:list sort)
  : Lemma (requires entries_scoped t cache 0 entries /\ k < L.length entries /\ L.memP s (scope_demanded t k))
          (ensures Some? (I.index_find cache k) /\
                   binder_judgment_scoped s (Some?.v (I.index_find cache k)) /\
                   premises_demanded t k (L.index entries k).binder_premises
                     (premise_scope_of (L.index entries k) s))
  = lemma_entries_scoped t cache 0 entries k;
    lemma_entry_scoped t k (L.index entries k) (Some?.v (I.index_find cache k)) (scope_demanded t k) s

(* --- The guard -------------------------------------------------------------------- *)

let lemma_guard (count work:nat) (c:binder_certificate) (cache:I.index_tree judgment)
  : Lemma (requires binder_scoped_within count work c cache)
          (ensures 0 <= c.binder_root /\ c.binder_root < L.length c.binder_entries /\
                   Some? (binder_scopes count work c) /\
                   L.memP [] (scope_demanded (fst (Some?.v (binder_scopes count work c))) c.binder_root) /\
                   entries_scoped (fst (Some?.v (binder_scopes count work c))) cache 0 c.binder_entries)
  = let t, w = Some?.v (binder_scopes count work c) in
    lemma_count_cells 0 c.binder_entries;
    FStar.List.Tot.Properties.mem_memP [] (scope_demanded t c.binder_root);
    lemma_entries_checked t cache 0 c.binder_entries w

(* Theorem 1: the root is an entry, assigned `[]`, and scoped at `[]`. *)
let lemma_root_scoped (count work:nat) (c:binder_certificate) (cache:I.index_tree judgment)
  : Lemma (requires binder_scoped_within count work c cache)
          (ensures 0 <= c.binder_root /\ c.binder_root < L.length c.binder_entries /\
                   Some? (I.index_find cache c.binder_root) /\
                   binder_judgment_scoped [] (Some?.v (I.index_find cache c.binder_root)))
  = lemma_guard count work c cache;
    let t = fst (Some?.v (binder_scopes count work c)) in
    lemma_scoped_at t cache c.binder_entries c.binder_root []

(* Theorem 2: every edge used at an assigned scope is scoped under the user's
   binders. *)
let lemma_edge_scoped (count work:nat) (c:binder_certificate) (cache:I.index_tree judgment)
                      (t:scope_demands) (k:nat) (s:list sort) (p:int)
  : Lemma (requires binder_scoped_within count work c cache /\ Some? (binder_scopes count work c) /\
                    fst (Some?.v (binder_scopes count work c)) == t /\
                    k < L.length c.binder_entries /\ L.memP s (scope_demanded t k) /\
                    L.memP p (L.index c.binder_entries k).binder_premises)
          (ensures (let s' = premise_scope_of (L.index c.binder_entries k) s in
                    Some? (I.index_find cache k) /\ binder_judgment_scoped s (Some?.v (I.index_find cache k)) /\
                    0 <= p /\ p < k /\ L.memP s' (scope_demanded t p) /\
                    Some? (I.index_find cache p) /\ binder_judgment_scoped s' (Some?.v (I.index_find cache p))))
  = lemma_guard count work c cache;
    lemma_scoped_at t cache c.binder_entries k s;
    let s' = premise_scope_of (L.index c.binder_entries k) s in
    lemma_premises_demanded t k (L.index c.binder_entries k).binder_premises s' p;
    lemma_scoped_at t cache c.binder_entries p s'

(* For the checker: an accepted certificate passed the guard on the checker's
   own cache, and its conclusion is scoped at `[]`. *)
let lemma_checked_guard (skolems:list SK.definition) (assertions:list judgment)
                        (c:binder_certificate) (concl:judgment)
  : Lemma (requires check_binder_with_context skolems assertions c concl)
          (ensures Some? (check_binder_entries skolems assertions c.binder_entries I.Empty 0) /\
                   (let cache = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
                    let n = L.length c.binder_entries in
                    I.index_find cache c.binder_root == Some concl /\
                    binder_scoped_within (binder_demand_limit n) (binder_work_limit n) c cache))
  = lemma_count_cells 0 c.binder_entries

let lemma_checked_root_scoped (skolems:list SK.definition) (assertions:list judgment)
                              (c:binder_certificate) (concl:judgment)
  : Lemma (requires check_binder_with_context skolems assertions c concl)
          (ensures binder_judgment_scoped [] concl)
  = lemma_checked_guard skolems assertions c concl;
    let cache = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
    let n = L.length c.binder_entries in
    lemma_root_scoped (binder_demand_limit n) (binder_work_limit n) c cache
