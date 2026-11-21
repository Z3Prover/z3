module Z3BinderScopeSyntax

open Z3AstTheory
open Z3UnifiedProofSyntax
open Z3ProofIndex
module L = FStar.List.Tot

(* --- Scopes of binder entries ----------------------------------------------- *)

(* A certificate's entries are judgments at different binder depths: the
   premise of a quantifier-introduction entry is the body judgment, open under
   the entry's binders. `check_binder_entries` does not check scopes, so an
   entry whose variables disagree with the binders that bind them (for example
   `Var 0` annotated Bool under an Int binder) was accepted, and the Boolean
   wrapper of `binder_quantifier_step` could then certify a false equation
   between quantifiers. `binder_scoped` assigns every entry the scopes at which
   the root uses it and requires the entry's judgment to be scoped
   (`Z3Definitions.scoped`) at each of them:

   * the root is an entry index and is used at the closed top-level scope `[]`;
   * an entry used at `scope` with binder sorts `bs` uses its premises at
     `L.rev bs @ scope` (`Var 0` is the last binder), any other entry at
     `scope` itself; every premise must be an earlier entry;
   * one entry may be used at several scopes (a closed subproof inside and
     outside a binder, or a shared body proof under different binders); it is
     checked at each. Entries the root does not use get no scope and no check.

   The scopes are collected backwards (premises precede their users). The
   forward check confirms, for every scope of every entry, that the entry's
   judgment is scoped there and that each premise is an earlier entry that was
   assigned the scope its user needs; it does not rely on the backward pass.
   `Z3BinderScope` proves what an accepted certificate then satisfies.

   Resources. Shared entries under differently nested binders can need
   exponentially many scopes, and `Z3Definitions.scoped` walks expressions
   and sorts as trees (shared subterms and shared sorts are walked again).
   The guard is therefore bounded, and exceeding a bound rejects the
   certificate (the node keeps a pending obligation):

   * a DEMANDED (stored) scope has at most `binder_scope_limit` sorts,
     checked before it is built; an entry is assigned at most
     `binder_entry_scope_limit` scopes; at most `binder_demand_limit n`
     scopes are assigned for `n` entries;
   * both passes share one work budget, `binder_work_limit n` units, and
     every step is charged before it is taken: one unit per entry, per index
     lookup or update, per list cell counted or compared, per expression node
     walked, per sort node compared (both sorts are walked together, so a
     comparison costs at most the smaller unfolded sort), the lengths of both
     names (`name_length`, which equals `FStar.String.strlen`) before two
     base-sort names are compared, and one unit per variable index step;
     `2 m + 1` units to build the scope under `m` binders, also inside
     expressions, where scopes are not capped by `binder_scope_limit` but
     every cell built or indexed is charged; and `len + 2` units per assigned
     scope of length `len`.

   Stack. The guard's walks are loops (self tail calls, which the Cherry
   backend compiles to `goto`): the scope under `bs` is built by
   `scope_under`, which equals `L.rev bs @ scope`; the expression walk
   (`scoped_frames_within`) and the sort comparison (`sort_tasks_within`)
   keep their pending work on explicit worklists, with at most two new cells
   per step; every step on a sort task or an expression node, but a failing
   last one, is charged at least a unit, and popping a finished expression
   frame is free (one pop per frame, and frames are pushed only by the
   walk's start and by charged steps); the list and name counts are loops.
   They compute exactly the results and the work left of the recursive
   functions of 0ebb92579 (`Z3BinderScope.lemma_scope_under`,
   `lemma_scoped_same`, `lemma_sort_same`, `lemma_premise_scope_same`),
   whose recursion was as deep as the expression, the sort or the binder
   list on the Cherry backend. This is not a stack bound for the whole
   checker.
   `check_binder_entries`, which runs before the guard, is also a loop on
   the Cherry backend: its option binds are inlined
   (`Z3ProofIndex.bind_opt`), so its recursive call is a self tail call.

   The units are an abstract count, not a time bound: a lookup in
   `Z3ProofIndex.index_tree` costs up to `log2 n + 1` steps, and an integer
   (bignum) comparison or update is one primitive operation. The two names'
   lengths are computed before they are charged: both runtimes decode one
   character per UTF-8 lead byte (`ocaml_runtime/fStar_String.ml` decodes
   like the Cherry runtime; the OCaml build calls it in place of F*'s
   Batteries-based `list_of_string`), in as many steps as the count and
   about twice as many transient list cells (the decoded list and its
   reversal), and the count is at least a quarter of the name's bytes also
   for malformed UTF-8;
   the count is a tail-recursive loop, so it needs no stack proportional to
   the name. The uncharged work is therefore that of the two names of the
   one comparison whose charge exceeds the remaining budget (neither name
   need exceed it alone): at most the budget plus both names' bytes, up to
   constant factors. Comparing two names costs at most four units per
   charged character. Linear passes over the entry list itself (its length
   and reversal), and `check_binder_entries`, which runs before the guard,
   are not charged; the budget bounds the guard's own work. The guard only
   rejects certificates; it accepts nothing new. *)
let binder_scope_limit : nat = 1024

let binder_entry_scope_limit : nat = 64

let binder_demand_limit (n:nat) : nat = 4 * n + 1024

(* 65536 units per entry: the expression budget the document layer allows one
   input (`Z3ProofDocument.document_definitions`). *)
let binder_work_limit (n:nat) : nat = 65536 * (n + 1)

let scope_charge (work cost:nat) : option nat =
  if cost <= work then Some (work - cost) else None

(* `acc` plus the length of `l`, one unit per element, by a self tail call: the
   Cherry backend compiles it to a loop (`goto`), so it needs no stack in the
   length of `l` (a binder list can be as long as the work allows). *)
let rec scope_length_acc (#a:Type) (work acc:nat) (l:list a)
  : Tot (option (nat & nat)) (decreases l) =
  match l with
  | [] -> Some (acc, work)
  | _ :: rest -> if work = 0 then None else scope_length_acc (work - 1) (acc + 1) rest

(* The length of `l` and the work left, one unit per element; `None` when `l`
   is longer than `work` (`Z3BinderScope.lemma_length_acc`). *)
let scope_length_within (#a:Type) (work:nat) (l:list a) : option (nat & nat) =
  scope_length_acc work 0 l

(* The number of elements of `l` plus `acc`, by a self tail call: the Cherry
   backend compiles it to a loop (`goto`), so it needs no stack in the length
   of `l`. *)
let rec count_cells (#a:Type) (acc:nat) (l:list a) : Tot nat (decreases l) =
  match l with
  | [] -> acc
  | _ :: rest -> count_cells (acc + 1) rest

(* The length of a name, as `FStar.String.strlen` counts it
   (`Z3BinderScope.lemma_name_length`): the characters of
   `FStar.String.list_of_string`. `strlen` itself is `List.Tot.length` of that
   list, which the Cherry backend compiled, at the nightly F* pin before
   2026-10-30, to a recursion as deep as the name (a native stack overflow on
   names of a few hundred thousand characters). `FStar.String.length` is not
   used: the Cherry runtime computes it by counting the bytes that are not
   UTF-8 continuation bytes, which a malformed name can make zero. *)
let name_length (s:string) : nat = count_cells 0 (FStar.String.list_of_string s)

(* The scope under the binder sorts `bs`, `L.rev bs @ scope` (`Var 0` is the
   last binder; `Z3BinderScope.lemma_scope_under`), by a self tail call: the
   Cherry backend compiles it to a loop (`goto`), so it needs no stack in the
   length of `bs`, which inside an expression is bounded only by the work.
   `L.append` is a recursion as deep as `bs` on the Cherry backend. This is
   `L.rev_acc bs scope` (`Z3BinderScope.lemma_scope_under_rev_acc`), written
   here when the OCaml runtime stand-in (`ocaml_runtime/fStar_List_Tot_Base.ml`)
   did not provide `rev_acc`. *)
let rec scope_under (bs scope:list sort) : Tot (list sort) (decreases bs) =
  match bs with
  | [] -> scope
  | b :: rest -> scope_under rest (b :: scope)

(* One task of the sort comparison: two sorts, or two sort lists compared
   cell by cell. *)
type sort_task =
  | SortPair : sort -> sort -> sort_task
  | SortListPair : list sort -> list sort -> sort_task

(* The units charged before two base-sort names are compared: both names'
   lengths, `name_length a + name_length b` (`Z3BinderScope.lemma_name_pair_units`).
   Equal names (a well-sorted argument against its declared domain sort, a
   variable against its scope sort) are counted once and the count doubled: on
   the Cherry backend a count decodes the name into a list of characters
   (`FStar.String.list_of_string`) and frees it again, and the scope-entry pass
   compares base sorts at every argument of every node it walks. The charge, the
   result and the work left are unchanged. *)
let name_pair_units (a b:string) : nat =
  if a = b then (let n = name_length a in n + n) else name_length a + name_length b

(* `sort_eq s t` and `sort_list_eq l1 l2` (structural sort equality) for the
   tasks in order, one unit per sort node and list cell visited, and the two
   names' lengths before two base-sort names are compared; the first unequal
   pair or exhausted budget ends the comparison. The pending comparisons are
   an explicit worklist and the function is a self tail call, which the
   Cherry backend compiles to a loop (`goto`): it needs no stack in the depth
   of the sorts. Each step charges a unit and pushes at most two tasks, so the
   worklist cells allocated are at most twice the units charged. It computes
   exactly what the recursive comparison of d50187500/0ebb92579 computed,
   result and work left (`Z3BinderScope.lemma_sort_same`). *)
let rec sort_tasks_within (work:nat) (tasks:list sort_task)
  : Tot (option (bool & nat)) (decreases work) =
  match tasks with
  | [] -> Some (true, work)
  | SortPair s t :: rest ->
    (match scope_charge work 1 with
     | None -> None
     | Some w ->
       (match s, t with
        | BaseSort a, BaseSort b ->
          (match scope_charge w (name_pair_units a b) with
           | Some w' -> if a = b then sort_tasks_within w' rest else Some (false, w')
           | None -> None)
        | ArraySort d1 r1, ArraySort d2 r2 ->
          sort_tasks_within w (SortListPair d1 d2 :: SortPair r1 r2 :: rest)
        | SortApp k1 a1, SortApp k2 a2 ->
          if k1 = k2 then sort_tasks_within w (SortListPair a1 a2 :: rest)
          else Some (false, w)
        | _, _ -> Some (false, w)))
  | SortListPair l1 l2 :: rest ->
    (match scope_charge work 1 with
     | None -> None
     | Some w ->
       (match l1, l2 with
        | [], [] -> sort_tasks_within w rest
        | a :: l1', b :: l2' -> sort_tasks_within w (SortPair a b :: SortListPair l1' l2' :: rest)
        | _, _ -> Some (false, w)))

let sort_eq_within (work:nat) (s t:sort) : option (bool & nat) =
  sort_tasks_within work [SortPair s t]

let sort_list_eq_within (work:nat) (l1 l2:list sort) : option (bool & nat) =
  sort_tasks_within work [SortListPair l1 l2]

(* `sorts_match args dom`. *)
let rec sorts_match_within (work:nat) (args:list expr) (dom:list sort)
  : Tot (option (bool & nat)) (decreases args) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    (match args, dom with
     | [], [] -> Some (true, w)
     | a :: args', d :: dom' ->
       (match sort_eq_within w (get_sort a) d with
        | Some (true, w') -> sorts_match_within w' args' dom'
        | r -> r)
     | _, _ -> Some (false, w))

(* Whether `scope` is among `scopes`. *)
let rec scope_mem_within (work:nat) (scope:list sort) (scopes:list (list sort))
  : Tot (option (bool & nat)) (decreases scopes) =
  match scopes with
  | [] -> Some (false, work)
  | x :: rest ->
    (match sort_list_eq_within work x scope with
     | Some (true, w) -> Some (true, w)
     | Some (false, w) -> scope_mem_within w scope rest
     | None -> None)

(* The sort at index `n` of `scope`. *)
let rec scope_nth (scope:list sort) (n:nat) : Tot (option sort) (decreases scope) =
  match scope with
  | [] -> None
  | s :: rest -> if n = 0 then Some s else scope_nth rest (n - 1)

(* Expression nodes, the termination measure of `scoped_frames_within`
   (proof only, not extracted). *)
noextract
let rec expr_nodes (e:expr) : Tot nat (decreases e) =
  match e with
  | Var _ _ -> 1
  | App _ args -> 1 + expr_list_nodes args
  | Quantifier _ _ _ b -> 1 + expr_nodes b

and expr_list_nodes (es:list expr) : Tot nat (decreases es) =
  match es with
  | [] -> 0
  | a :: rest -> expr_nodes a + expr_list_nodes rest

(* A frame of the scope check: the expressions still to be checked, in
   order, at a scope and its length. *)
type scope_frame = list sort & nat & list expr

noextract
let rec frame_nodes (frames:list scope_frame) : Tot nat (decreases frames) =
  match frames with
  | [] -> 0
  | (_, _, es) :: rest -> expr_list_nodes es + frame_nodes rest

(* `Z3Definitions.scoped scope e` for every expression of every frame, in
   order, for `len` the length of `scope`; the first expression that is not
   scoped, or the exhausted budget, ends the check. The pending expressions
   are an explicit worklist of frames and the function is a self tail call,
   which the Cherry backend compiles to a loop (`goto`): it needs no stack in
   the depth of the expression. Each expression node allocates at most two
   frames and, unless its first charge fails and ends the check, is charged
   at least a unit; popping an exhausted frame allocates nothing. It computes
   exactly what the recursive walk of
   d50187500/0ebb92579 computed, result and work left
   (`Z3BinderScope.lemma_scoped_same`). *)
let rec scoped_frames_within (work:nat) (frames:list scope_frame)
  : Tot (option (bool & nat)) (decreases %[frame_nodes frames; L.length frames]) =
  match frames with
  | [] -> Some (true, work)
  | (_, _, []) :: rest -> scoped_frames_within work rest
  | (scope, len, e :: es) :: rest ->
    let rest' = (scope, len, es) :: rest in
    (match scope_charge work 1 with
     | None -> None
     | Some w ->
       (match e with
        | Var n s ->
          if n < len then
            (match scope_charge w (n + 1) with
             | Some w' ->
               (match scope_nth scope n with
                | Some s' ->
                  (match sort_eq_within w' s' s with
                   | Some (true, w'') -> scoped_frames_within w'' rest'
                   | r -> r)
                | None -> Some (false, w'))
             | None -> None)
          else Some (false, w)
        | App f args ->
          (match sorts_match_within w args f.domain with
           | Some (true, w') -> scoped_frames_within w' ((scope, len, args) :: rest')
           | r -> r)
        | Quantifier k bs s b ->
          (match scope_length_within w bs with
           | Some (m, w1) ->
             (match scope_charge w1 (2 * m + 1) with
              | Some w2 ->
                (match sort_eq_within w2 s (quant_sort k bs (get_sort b)) with
                 | Some (true, w3) ->
                   (match (if k = Lambda_k then Some (true, w3) else sort_eq_within w3 (get_sort b) bool_sort) with
                    | Some (true, w4) -> scoped_frames_within w4 ((scope_under bs scope, m + len, [b]) :: rest')
                    | r -> r)
                 | r -> r)
              | None -> None)
           | None -> None)))

(* `Z3Definitions.scoped scope e`, for `len` the length of `scope`. *)
let scoped_within (work:nat) (scope:list sort) (len:nat) (e:expr) : option (bool & nat) =
  scoped_frames_within work [(scope, len, [e])]

(* `Z3Definitions.scoped_args scope args`. *)
let scoped_args_within (work:nat) (scope:list sort) (len:nat) (args:list expr) : option (bool & nat) =
  scoped_frames_within work [(scope, len, args)]

let judgment_scoped_within (work:nat) (scope:list sort) (len:nat) (j:judgment)
  : option (bool & nat) =
  match j with
  | Holds e -> scoped_within work scope len e
  | Equal a b | Observational a b ->
    (match scoped_within work scope len a with
     | Some (true, w) -> scoped_within w scope len b
     | r -> r)

(* The scope of an entry's premises, and its length, when the entry is used
   at `scope` of length `len`; `None` beyond `binder_scope_limit`. *)
let binder_premise_scope_within (work:nat) (e:binder_entry) (scope:list sort) (len:nat)
  : option (list sort & nat & nat) =
  match e.binder_sorts with
  | None -> Some (scope, len, work)
  | Some bs ->
    (match scope_length_within work bs with
     | Some (m, w) ->
       if m + len > binder_scope_limit then None
       else (match scope_charge w (2 * m + 1) with
             | Some w' -> Some (scope_under bs scope, m + len, w')
             | None -> None)
     | None -> None)

type scope_demands = Z3ProofIndex.index_tree (list (list sort))

let scope_demanded (t:scope_demands) (k:int) : list (list sort) =
  match Z3ProofIndex.index_find t k with
  | Some scopes -> scopes
  | None -> []

(* Assign `scope` (of length `len`) to the entry `k`; `count` assignments and
   `work` units are left. *)
let scope_demand (t:scope_demands) (k:nat) (scope:list sort) (len:nat) (count work:nat)
  : option (scope_demands & nat & nat) =
  match scope_charge work 1 with
  | None -> None
  | Some w ->
    let old = scope_demanded t k in
    (match scope_mem_within w scope old with
     | Some (true, w1) -> Some (t, count, w1)
     | Some (false, w1) ->
       (match scope_length_within w1 old with
        | Some (m, w2) ->
          if count = 0 || m >= binder_entry_scope_limit then None
          else (match scope_charge w2 (len + 2) with
                | Some w3 -> Some (Z3ProofIndex.index_put t k (scope :: old), count - 1, w3)
                | None -> None)
        | None -> None)
     | None -> None)

(* The premises `ps` of the entry `k`, used at `scope`. *)
let rec scope_demand_premises (t:scope_demands) (k:int) (ps:list int) (scope:list sort) (len:nat)
                              (count work:nat)
  : Tot (option (scope_demands & nat & nat)) (decreases ps) =
  match ps with
  | [] -> Some (t, count, work)
  | p :: rest ->
    if 0 <= p && p < k then
      (match scope_demand t p scope len count work with
       | Some (t', count', work') -> scope_demand_premises t' k rest scope len count' work'
       | None -> None)
    else None

let rec scope_demand_entry (t:scope_demands) (k:int) (e:binder_entry) (scopes:list (list sort))
                           (count work:nat)
  : Tot (option (scope_demands & nat & nat)) (decreases scopes) =
  match scopes with
  | [] -> Some (t, count, work)
  | s :: rest ->
    (match scope_length_within work s with
     | Some (len, w) ->
       (match binder_premise_scope_within w e s len with
        | Some (s', len', w') ->
          (match scope_demand_premises t k e.binder_premises s' len' count w' with
           | Some (t', count', work') -> scope_demand_entry t' k e rest count' work'
           | None -> None)
        | None -> None)
     | None -> None)

(* `reversed` lists the entries last first; `k` is the index of its head. *)
let rec scope_demand_entries (t:scope_demands) (k:int) (reversed:list binder_entry) (count work:nat)
  : Tot (option (scope_demands & nat)) (decreases reversed) =
  match reversed with
  | [] -> Some (t, work)
  | e :: rest ->
    (match scope_charge work 1 with
     | Some w ->
       (match scope_demand_entry t k e (scope_demanded t k) count w with
        | Some (t', count', work') -> scope_demand_entries t' (k - 1) rest count' work'
        | None -> None)
     | None -> None)

let rec scope_premises_demanded (t:scope_demands) (k:int) (ps:list int) (scope:list sort) (work:nat)
  : Tot (option nat) (decreases ps) =
  match ps with
  | [] -> Some work
  | p :: rest ->
    if 0 <= p && p < k then
      (match scope_charge work 1 with
       | Some w ->
         (match scope_mem_within w scope (scope_demanded t p) with
          | Some (true, w') -> scope_premises_demanded t k rest scope w'
          | _ -> None)
       | None -> None)
    else None

let rec scope_entry_checked (t:scope_demands) (k:int) (e:binder_entry) (j:judgment)
                            (scopes:list (list sort)) (work:nat)
  : Tot (option nat) (decreases scopes) =
  match scopes with
  | [] -> Some work
  | s :: rest ->
    (match scope_length_within work s with
     | Some (len, w) ->
       (match judgment_scoped_within w s len j with
        | Some (true, w1) ->
          (match binder_premise_scope_within w1 e s len with
           | Some (s', _, w2) ->
             (match scope_premises_demanded t k e.binder_premises s' w2 with
              | Some w3 -> scope_entry_checked t k e j rest w3
              | None -> None)
           | None -> None)
        | _ -> None)
     | None -> None)

let rec scope_entries_checked (t:scope_demands) (cache:Z3ProofIndex.index_tree judgment) (k:nat)
                              (entries:list binder_entry) (work:nat)
  : Tot (option nat) (decreases entries) =
  match entries with
  | [] -> Some work
  | e :: rest ->
    (match scope_charge work 1 with
     | Some w ->
       (match Z3ProofIndex.index_find cache k with
        | Some j ->
          (match scope_entry_checked t k e j (scope_demanded t k) w with
           | Some w' -> scope_entries_checked t cache (k + 1) rest w'
           | None -> None)
        | None -> None)
     | None -> None)

(* The scopes assigned by the backward pass, starting from the root at `[]`,
   and the work left; `None` when a bound is exceeded or a premise is not an
   earlier entry. The guard counts entries with `count_cells` (a loop), which
   is `L.length` (`Z3BinderScope.lemma_count_cells`). *)
let binder_scopes (count work:nat) (certificate:binder_certificate) : option (scope_demands & nat) =
  let n = count_cells 0 certificate.binder_entries in
  let root = certificate.binder_root in
  if 0 <= root && root < n then
    scope_demand_entries (Z3ProofIndex.index_put Z3ProofIndex.Empty root [[]]) (n - 1)
                         (L.rev certificate.binder_entries) count work
  else None

(* The guard with explicit bounds (the checker uses `binder_demand_limit` and
   `binder_work_limit`). *)
let binder_scoped_within (count work:nat) (certificate:binder_certificate)
                         (cache:Z3ProofIndex.index_tree judgment) : bool =
  let root = certificate.binder_root in
  0 <= root && root < count_cells 0 certificate.binder_entries &&
  (match binder_scopes count work certificate with
   | Some (t, w) ->
     L.mem [] (scope_demanded t root) &&
     Some? (scope_entries_checked t cache 0 certificate.binder_entries w)
   | None -> false)

let binder_scoped (certificate:binder_certificate) (cache:Z3ProofIndex.index_tree judgment) : bool =
  let n = count_cells 0 certificate.binder_entries in
  binder_scoped_within (binder_demand_limit n) (binder_work_limit n) certificate cache

