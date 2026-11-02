(*
   Z3CheckedExpansion.fst

   Definition expansion on the checked graph of the opt-in mode
   `verified-dag-v1`: from a node of an invariant graph, the node that stores
   `Z3Definitions.expand fuel defs` of its expression, built on the graph.

   * `glift a c g m x`: the node storing `D.lift a c (value_of g x)` (a lift
     by 0 is the node itself);
   * `ginst vars an g x`: the node storing `D.instantiate 0 vars avs (value_of g x)`,
     `avs` the expressions of the argument nodes `an`;
   * `intern_expr g e`: a node storing the expression `e` (a definition's
     body, which the document gives as an expression, not as a node; it is
     imported as a tree, each subexpression charged);
   * `expand_nodes defs f g bodies xs`: the nodes storing `D.expand f defs` of
     the expressions of `xs`, in order; `bodies` holds the nodes of the bodies
     imported before with the same `defs` (by position in `defs`), reused and
     extended (`Z3DagDocument` keeps them for one document's check).

   Each is an explicit worklist loop (a self tail call), so its stack does not
   grow with the depth of an expression. A node is rebuilt from the nodes of
   its rebuilt children, which a loop finds in its memo, keyed by the node and
   its context: (shift, cutoff) for a lift, the binder depth for an
   instantiation, the fuel for an expansion. A memo lives in one call (one set
   of definitions, one argument list), and is never taken from another. A
   frame is checked again when it is taken from the worklist (the node's
   shape, its children's entries in the memo), so the worklist carries no
   invariant, except the frame that expands the instance of a definition
   (`EThen`), which carries its equation (`frame_ok`).

   The spec functions (`D.lift`, `D.instantiate`, `D.expand`) appear only in
   the invariants: the loops read nodes and stored expressions by id and never
   compare expressions. The children of an unchanged node are compared by id
   (`CS.same_ids`), and a rebuilt quantifier only when its body has the sort id
   of the old one; a node whose sort conditions do not hold is not rebuilt
   (`BuildInvalid`), nor is a quantifier whose sort would change.

   Units, from the graph's own budgets: a frame taken `memo_units` of
   Preparation, `memo_units` of Storage per memo entry, a Storage unit per
   frame or child cell pushed, `table_units` of Preparation per child looked
   up, a unit per definition compared when a declaration is looked up, a unit
   per argument variable compared, and the builders' and interning's own.
   The structural equality of the declarations compared by a lookup (as in
   `Z3Definitions.lookup`) is counted as one unit per definition, not by the
   size of the declarations.
*)
module Z3CheckedExpansion

open Z3AstTheory
module L = FStar.List.Tot
module I = Z3ProofIndex
module CS = Z3CheckedSorts
module T = Z3CheckedTerms
module CG = Z3CheckedGraph
module D = Z3Definitions

let lift_index (a c n:nat) : nat = if n < c then n else n + a

(* --- Sorts are kept by lifting ---------------------------------------------------------------- *)

let lemma_lift_sort (a c:nat) (e:expr) : Lemma (get_sort (D.lift a c e) == get_sort e) =
  match e with Var _ _ -> () | App _ _ -> () | Quantifier _ _ _ _ -> ()

(* --- Charging ------------------------------------------------------------------------------------ *)

let charge (g:CG.cgraph) (p s:nat) : option CG.cgraph =
  if g.CG.prep < p || g.CG.store < s then None
  else Some ({ g with CG.prep = g.CG.prep - p; CG.store = g.CG.store - s })

let lemma_charge (g:CG.cgraph) (p s:nat)
  : Lemma (requires CG.graph_inv g)
          (ensures (match charge g p s with
                    | Some g' -> CG.graph_inv g' /\ CG.cgrows g g' /\ CG.node_count g' == CG.node_count g
                    | None -> True))
  = if g.CG.prep < p || g.CG.store < s then ()
    else CG.lemma_budget g (g.CG.prep - p) (g.CG.store - s)

let memo_units : nat = 3 * CS.table_units

(* --- Constructors: one node from the nodes of its rebuilt children -------------------------------- *)

(* The variable of `x` with its index lifted. *)
let lift_var (a c:nat) (g:CG.cgraph) (x:nat) : CG.built =
  match CG.node_of g x, CG.value_of g x with
  | Some (T.ENVar _ i), Some (Var n s) -> CG.add_var g (lift_index a c n) (s, i)
  | _, _ -> CG.BuildInvalid

let lifted (a c:nat) (g g':CG.cgraph) (x y:nat) : prop =
  CG.graph_inv g' /\ CG.cgrows g g' /\ y < CG.node_count g' /\
  (match CG.value_of g x with Some v -> CG.value_of g' y == Some (D.lift a c v) | None -> False)

let lemma_lift_var (a c:nat) (g:CG.cgraph) (x:nat)
  : Lemma (requires CG.graph_inv g /\ x < CG.node_count g)
          (ensures (match lift_var a c g x with CG.Built g' y -> lifted a c g g' x y | _ -> True))
  = assert (CG.node_exact g x);
    CG.reveal_exact g x;
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENVar _ i), Some (Var n s) -> CG.lemma_add_var g (lift_index a c n) (s, i)
    | _, _ -> ()

(* The application of `x`'s declaration to the nodes `ys`: its domain the
   sort ids of `x`'s own children (read and charged), its range `x`'s. *)
let rebuild_app (g:CG.cgraph) (x:nat) (ys:list nat) : CG.built =
  match CG.node_of g x, CG.value_of g x with
  | Some (T.ENApp ok xs i), Some (App f _) ->
    if not ok then CG.BuildInvalid
    else (match CG.read_children g xs [] [] g.CG.prep g.CG.store with
          | CG.ChildrenRead _ ss p s ->
            CG.add_app ({ g with CG.prep = p; CG.store = s }) ({ CG.decl = f; CG.dom = ss; CG.rng = i }) ys
          | CG.ChildrenExhausted ph -> CG.BuildExhausted ph
          | CG.ChildrenInvalid -> CG.BuildInvalid)
  | _, _ -> CG.BuildInvalid

let app_rebuilt (g g':CG.cgraph) (x y:nat) (ys:list nat) : prop =
  CG.graph_inv g' /\ CG.cgrows g g' /\ y < CG.node_count g' /\
  (match CG.value_of g x, CG.values_of g ys with
   | Some (App f _), Some vs -> CG.value_of g' y == Some (App f vs)
   | _, _ -> False)

let rec lemma_values_same (g g':CG.cgraph) (xs:list nat)
  : Lemma (requires g'.CG.values == g.CG.values) (ensures CG.values_of g' xs == CG.values_of g xs) (decreases xs)
  = match xs with [] -> () | _ :: rest -> lemma_values_same g g' rest

let lemma_rebuilt_app (g g1:CG.cgraph) (d:CG.cdecl) (x:nat) (ys:list nat) (f:func_decl)
  : Lemma (requires CG.graph_inv g1 /\ CG.cgrows g g1 /\ g1.CG.values == g.CG.values /\ CG.decl_ok g1 d /\
                    d.CG.decl == f /\ (match CG.value_of g x with Some (App f' _) -> f' == f | _ -> False))
          (ensures (match CG.add_app g1 d ys with CG.Built g' y -> app_rebuilt g g' x y ys | _ -> True))
  = CG.lemma_add_app g1 d ys;
    lemma_values_same g g1 ys;
    match CG.add_app g1 d ys with
    | CG.Built g' _ -> CG.lemma_cgrows_trans g g1 g'
    | _ -> ()

let lemma_rebuild_app (g:CG.cgraph) (x:nat) (ys:list nat)
  : Lemma (requires CG.graph_inv g /\ x < CG.node_count g)
          (ensures (match rebuild_app g x ys with CG.Built g' y -> app_rebuilt g g' x y ys | _ -> True))
  = assert (CG.node_exact g x);
    CG.reveal_exact g x;
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENApp ok xs i), Some (App f args) ->
      if not ok then ()
      else begin
        CG.lemma_read_children_ok g xs g.CG.prep g.CG.store;
        match CG.read_children g xs [] [] g.CG.prep g.CG.store with
        | CG.ChildrenRead vs ss p s ->
          let g1 = { g with CG.prep = p; CG.store = s } in
          CG.lemma_budget g p s;
          T.lemma_sorts_match_map args f.domain;
          let d = { CG.decl = f; CG.dom = ss; CG.rng = i } in
          assert (CG.decl_ok g1 d);
          lemma_rebuilt_app g g1 d x ys f
        | _ -> ()
      end
    | _, _ -> ()

let rec pair_sorts (bs:list sort) (ids:list nat) : Tot (list CG.csort) (decreases bs) =
  match bs, ids with
  | b :: bs', i :: ids' -> (b, i) :: pair_sorts bs' ids'
  | _, _ -> []

let rec lemma_pair_sorts (g:CG.cgraph) (bs:list sort) (ids:list nat)
  : Lemma (requires CS.all_below ids (CG.sort_count g) /\ L.map (CG.interp g) ids == bs)
          (ensures CG.csorts_ok g (pair_sorts bs ids) /\ L.map fst (pair_sorts bs ids) == bs)
          (decreases bs)
  = match bs, ids with
    | _ :: bs', _ :: ids' -> lemma_pair_sorts g bs' ids'
    | _, _ -> ()

(* The quantifier of `x` (its kind and bound sorts, by their ids) over the
   body node `z`, when `z` has the sort id of `x`'s own body. *)
let rebuild_quant (g:CG.cgraph) (x z:nat) : CG.built =
  if z >= CG.node_count g then CG.BuildInvalid
  else
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENQuant ok ys y _), Some (Quantifier k bs _ _) ->
      (match CG.node_of g y, CG.node_of g z with
       | Some ny, Some nz ->
         if ok && CG.enode_sort ny = CG.enode_sort nz then CG.add_quant g k (pair_sorts bs ys) z
         else CG.BuildInvalid
       | _, _ -> CG.BuildInvalid)
    | _, _ -> CG.BuildInvalid

let quant_rebuilt (g g':CG.cgraph) (x z w:nat) : prop =
  CG.graph_inv g' /\ CG.cgrows g g' /\ w < CG.node_count g' /\
  (match CG.value_of g x, CG.value_of g z with
   | Some (Quantifier k bs q _), Some b' -> CG.value_of g' w == Some (Quantifier k bs q b')
   | _, _ -> False)

let lemma_rebuild_quant (g:CG.cgraph) (x z:nat)
  : Lemma (requires CG.graph_inv g /\ x < CG.node_count g)
          (ensures (match rebuild_quant g x z with CG.Built g' w -> quant_rebuilt g g' x z w | _ -> True))
  = if z >= CG.node_count g then ()
    else begin
      assert (CG.node_exact g x);
      CG.reveal_exact g x;
      match CG.node_of g x, CG.value_of g x with
      | Some (T.ENQuant ok ys y _), Some (Quantifier k bs q b) ->
        (match CG.node_of g y, CG.node_of g z with
         | Some ny, Some nz ->
           if ok && CG.enode_sort ny = CG.enode_sort nz then begin
             CG.lemma_node_sort g y;
             CG.lemma_node_sort g z;
             lemma_pair_sorts g bs ys;
             CG.lemma_add_quant g k (pair_sorts bs ys) z
           end
         | _, _ -> ())
      | _, _ -> ()
    end

(* --- Memos ------------------------------------------------------------------------------------------ *)

(* A lift's memo: for each (shift, cutoff, node) the node storing its lift. *)
type lift_memo = I.index_tree (I.index_tree (I.index_tree nat))

let memo_get (m:lift_memo) (a c x:nat) : option nat =
  match I.index_get m a with
  | Some ma -> (match I.index_get ma c with Some mc -> I.index_get mc x | None -> None)
  | None -> None

let memo_put (m:lift_memo) (a c x y:nat) : lift_memo =
  let ma = match I.index_get m a with Some t -> t | None -> I.Empty in
  let mc = match I.index_get ma c with Some t -> t | None -> I.Empty in
  I.index_put m a (I.index_put ma c (I.index_put mc x y))

let lemma_memo_put (m:lift_memo) (a c x y a' c' x':nat)
  : Lemma (memo_get (memo_put m a c x y) a' c' x' ==
           (if a' = a && c' = c && x' = x then Some y else memo_get m a' c' x'))
  = let ma = match I.index_get m a with Some t -> t | None -> I.Empty in
    let mc = match I.index_get ma c with Some t -> t | None -> I.Empty in
    I.lemma_index_put m a (I.index_put ma c (I.index_put mc x y)) a';
    I.lemma_index_put ma c (I.index_put mc x y) c';
    I.lemma_index_put mc x y x'

(* An instantiation's and an expansion's memo: (context, node) -> node. *)
type memo2 = I.index_tree (I.index_tree nat)

let get2 (m:memo2) (k x:nat) : option nat =
  match I.index_get m k with Some t -> I.index_get t x | None -> None

let put2 (m:memo2) (k x y:nat) : memo2 =
  let t = match I.index_get m k with Some t -> t | None -> I.Empty in
  I.index_put m k (I.index_put t x y)

let lemma_put2 (m:memo2) (k x y k' x':nat)
  : Lemma (get2 (put2 m k x y) k' x' == (if k' = k && x' = x then Some y else get2 m k' x'))
  = let t = match I.index_get m k with Some t -> t | None -> I.Empty in
    I.lemma_index_put m k (I.index_put t x y) k';
    I.lemma_index_put t x y x'

(* --- The lift of a node ------------------------------------------------------------------------- *)

(* `y` stores in `g` the lift of what `x` stores. *)
let lifted_in (a c:nat) (g:CG.cgraph) (x y:nat) : prop =
  x < CG.node_count g /\ y < CG.node_count g /\
  (match CG.value_of g x with Some v -> CG.value_of g y == Some (D.lift a c v) | None -> False)

let memo_ok (g:CG.cgraph) (m:lift_memo) : prop =
  forall (a c x:nat). (match memo_get m a c x with Some y -> lifted_in a c g x y | None -> True)

let lemma_memo_grows (g g':CG.cgraph) (m:lift_memo)
  : Lemma (requires CG.cgrows g g' /\ memo_ok g m) (ensures memo_ok g' m)
  = ()

let lemma_memo_extend (g:CG.cgraph) (m:lift_memo) (a c x y:nat)
  : Lemma (requires memo_ok g m /\ lifted_in a c g x y) (ensures memo_ok g (memo_put m a c x y))
  = let aux (a' c' x':nat)
      : Lemma (match memo_get (memo_put m a c x y) a' c' x' with Some y' -> lifted_in a' c' g x' y' | None -> True)
      = lemma_memo_put m a c x y a' c' x' in
    FStar.Classical.forall_intro_3 aux

let rec lemma_lifted_args (a c:nat) (g:CG.cgraph) (m:lift_memo) (xs:list nat) (args:list expr)
  : Lemma (requires memo_ok g m /\ CG.values_of g xs == Some args)
          (ensures (match I.opt_map (memo_get m a c) xs with
                    | Some ys -> CG.values_of g ys == Some (D.lift_args a c args)
                    | None -> True))
          (decreases xs)
  = match xs, args with
    | x :: xs', v :: args' ->
      lemma_lifted_args a c g m xs' args';
      (match memo_get m a c x with Some y -> assert (lifted_in a c g x y) | None -> ())
    | _, _ -> ()

let opt_map_tail_is (f:nat -> option nat) (xs:list nat)
  : Lemma (I.opt_map_tail f xs == I.opt_map f xs)
  = I.lemma_opt_map_acc f xs []

(* The nodes of an invariant graph all store an expression. *)
let rec lemma_values_some (g:CG.cgraph) (xs:list nat)
  : Lemma (requires CG.graph_inv g /\ CS.all_below xs (CG.node_count g)) (ensures Some? (CG.values_of g xs))
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: rest -> assert (CG.node_exact g x); CG.reveal_exact g x; lemma_values_some g rest

type lframe =
  | LEnter : c:nat -> x:nat -> lframe
  | LExit : c:nat -> x:nat -> lframe

let rec lenters (c:nat) (xs:list nat) (tail:list lframe) : Tot (list lframe) (decreases xs) =
  match xs with
  | [] -> tail
  | x :: rest -> lenters c rest (LEnter c x :: tail)

noeq
type lstep =
  | LNext : graph:CG.cgraph -> memo:lift_memo -> stack:list lframe -> lstep
  | LHalt : built:CG.built -> lstep

let lstep_ok (g:CG.cgraph) (r:lstep) : prop =
  match r with
  | LNext g' m' _ -> CG.graph_inv g' /\ CG.cgrows g g' /\ memo_ok g' m'
  | LHalt b -> ~(CG.Built? b)

(* A lift built from `g`: recorded in the memo, its update charged. *)
let lrecord (a c:nat) (g:CG.cgraph{CG.graph_inv g}) (m:lift_memo{memo_ok g m}) (x:nat{x < CG.node_count g})
            (b:CG.built) (rest:list lframe)
  : Pure lstep (requires (match b with CG.Built g' y -> lifted a c g g' x y | _ -> True))
               (ensures fun r -> lstep_ok g r) =
  match b with
  | CG.Built g' y ->
    lemma_memo_grows g g' m;
    (match charge g' 0 memo_units with
     | Some g'' ->
       lemma_charge g' 0 memo_units;
       lemma_memo_grows g' g'' m;
       CG.lemma_cgrows_trans g g' g'';
       lemma_memo_extend g'' m a c x y;
       LNext g'' (memo_put m a c x y) rest
     | None -> LHalt (CG.BuildExhausted T.Storage))
  | CG.BuildExhausted p -> LHalt (CG.BuildExhausted p)
  | CG.BuildInvalid -> LHalt CG.BuildInvalid

(* The lift `y` of `x`, already a node of `g` (`x` itself when the lift
   changes nothing), recorded in the memo (its update charged). *)
let lput (a c:nat) (g0 g:CG.cgraph) (m:lift_memo) (x y:nat) (rest:list lframe)
  : Pure lstep (requires CG.graph_inv g /\ memo_ok g m /\ CG.cgrows g0 g /\ lifted_in a c g x y)
               (ensures fun r -> lstep_ok g0 r) =
  match charge g 0 memo_units with
  | Some g1 ->
    lemma_charge g 0 memo_units;
    lemma_memo_grows g g1 m;
    CG.lemma_cgrows_trans g0 g g1;
    lemma_memo_extend g1 m a c x y;
    LNext g1 (memo_put m a c x y) rest
  | None -> LHalt (CG.BuildExhausted T.Storage)

let push (g:CG.cgraph{CG.graph_inv g}) (cells:nat) : r:option CG.cgraph{Some? r ==> (CG.graph_inv (Some?.v r) /\ CG.cgrows g (Some?.v r))} =
  lemma_charge g 0 cells; charge g 0 cells

let lift_enter (a c:nat) (g:CG.cgraph{CG.graph_inv g}) (m:lift_memo{memo_ok g m}) (x:nat) (rest:list lframe)
  : r:lstep{lstep_ok g r} =
  if x >= CG.node_count g then LHalt CG.BuildInvalid
  else match memo_get m a c x with
  | Some _ -> CG.lemma_cgrows_refl g; LNext g m rest
  | None ->
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENVar _ _), Some (Var n _) ->
      if lift_index a c n = n then (CG.lemma_cgrows_refl g; lput a c g g m x x rest)
      else (lemma_lift_var a c g x; lrecord a c g m x (lift_var a c g x) rest)
    | Some (T.ENApp _ xs _), Some (App _ _) ->
      (match push g (1 + L.length xs) with
       | Some g1 -> lemma_memo_grows g g1 m; LNext g1 m (lenters c xs (LExit c x :: rest))
       | None -> LHalt (CG.BuildExhausted T.Storage))
    | Some (T.ENQuant _ _ y _), Some (Quantifier _ bs _ _) ->
      (match push g 2 with
       | Some g1 -> lemma_memo_grows g g1 m; LNext g1 m (LEnter (c + L.length bs) y :: LExit c x :: rest)
       | None -> LHalt (CG.BuildExhausted T.Storage))
    | _, _ -> LHalt CG.BuildInvalid

let lift_exit_app (a c:nat) (g:CG.cgraph{CG.graph_inv g}) (m:lift_memo{memo_ok g m}) (x:nat{x < CG.node_count g})
                  (xs:list nat) (rest:list lframe)
  : Pure lstep (requires (match CG.node_of g x, CG.value_of g x with
                          | Some (T.ENApp _ xs' _), Some (App _ _) -> xs' == xs
                          | _, _ -> False))
               (ensures fun r -> lstep_ok g r) =
  match charge g (L.length xs * CS.table_units) 0 with
  | None -> LHalt (CG.BuildExhausted T.Preparation)
  | Some g1 ->
    lemma_charge g (L.length xs * CS.table_units) 0;
    lemma_memo_grows g g1 m;
    assert (CG.node_exact g1 x);
    CG.reveal_exact g1 x;
    opt_map_tail_is (memo_get m a c) xs;
    match I.opt_map_tail (memo_get m a c) xs with
    | Some ys ->
      (match CG.value_of g1 x with
       | Some (App f args) ->
         lemma_lifted_args a c g1 m xs args;
         CS.lemma_same_ids ys xs;
         if CS.same_ids ys xs then lput a c g g1 m x x rest
         else begin
           lemma_rebuild_app g1 x ys;
           let r = lrecord a c g1 m x (rebuild_app g1 x ys) rest in
           r
         end)
    | None -> LHalt CG.BuildInvalid

let lift_exit_quant (a c:nat) (g:CG.cgraph{CG.graph_inv g}) (m:lift_memo{memo_ok g m}) (x:nat{x < CG.node_count g})
                    (y n:nat) (rest:list lframe)
  : Pure lstep (requires (match CG.node_of g x, CG.value_of g x with
                          | Some (T.ENQuant _ _ y' _), Some (Quantifier _ bs _ _) -> y' == y /\ n == L.length bs
                          | _, _ -> False))
               (ensures fun r -> lstep_ok g r) =
  assert (CG.node_exact g x);
  CG.reveal_exact g x;
  match memo_get m a (c + n) y with
  | Some z ->
    assert (lifted_in a (c + n) g y z);
    (match CG.value_of g x with
     | Some (Quantifier _ bs _ b) -> lemma_lift_sort a (c + n) b);
    if z = y then (CG.lemma_cgrows_refl g; lput a c g g m x x rest)
    else begin
      lemma_rebuild_quant g x z;
      lrecord a c g m x (rebuild_quant g x z) rest
    end
  | None -> LHalt CG.BuildInvalid

let lift_exit (a c:nat) (g:CG.cgraph{CG.graph_inv g}) (m:lift_memo{memo_ok g m}) (x:nat) (rest:list lframe)
  : r:lstep{lstep_ok g r} =
  if x >= CG.node_count g then LHalt CG.BuildInvalid
  else match memo_get m a c x with
  | Some _ -> CG.lemma_cgrows_refl g; LNext g m rest
  | None ->
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENApp _ xs _), Some (App _ _) -> lift_exit_app a c g m x xs rest
    | Some (T.ENQuant _ _ y _), Some (Quantifier _ bs _ _) -> lift_exit_quant a c g m x y (L.length bs) rest
    | _, _ -> LHalt CG.BuildInvalid

noeq
type lrun =
  | LRan : graph:CG.cgraph -> memo:lift_memo -> lrun
  | LStopped : built:CG.built -> lrun

(* The loop's invariant, opaque to the solver: the loop only passes it on. *)
[@@"opaque_to_smt"]
let linv_o (g:CG.cgraph) (m:lift_memo) : prop = CG.graph_inv g /\ memo_ok g m

let reveal_linv (g:CG.cgraph) (m:lift_memo) : Lemma (linv_o g m <==> (CG.graph_inv g /\ memo_ok g m))
  = FStar.Pervasives.reveal_opaque (`%linv_o) (linv_o g m)

let lrun_ok (g:CG.cgraph) (r:lrun) : prop =
  match r with
  | LRan g' m' -> linv_o g' m' /\ CG.cgrows g g'
  | LStopped b -> ~(CG.Built? b)

let lstep_ok_o (g:CG.cgraph) (r:lstep) : prop =
  match r with
  | LNext g' m' _ -> linv_o g' m' /\ CG.cgrows g g'
  | LHalt b -> ~(CG.Built? b)

let lemma_lrun_trans (g g1:CG.cgraph) (r:lrun)
  : Lemma (requires CG.cgrows g g1 /\ lrun_ok g1 r) (ensures lrun_ok g r)
  = match r with LRan g2 _ -> CG.lemma_cgrows_trans g g1 g2 | _ -> ()

(* One frame, charged `memo_units` of Preparation before it is taken. *)
let lift_frame (a:nat) (g:CG.cgraph) (m:lift_memo) (fr:lframe) (rest:list lframe)
  : Pure lstep (requires linv_o g m) (ensures fun r -> lstep_ok_o g r) =
  reveal_linv g m;
  match charge g memo_units 0 with
  | None -> LHalt (CG.BuildExhausted T.Preparation)
  | Some g0 ->
    lemma_charge g memo_units 0;
    lemma_memo_grows g g0 m;
    let s = match fr with LEnter c x -> lift_enter a c g0 m x rest | LExit c x -> lift_exit a c g0 m x rest in
    (match s with LNext g1 m1 _ -> CG.lemma_cgrows_trans g g0 g1; reveal_linv g1 m1 | _ -> ());
    s

(* The worklist of a lift with shift `a`: a self tail call. *)
let rec lift_loop (a:nat) (g:CG.cgraph) (m:lift_memo) (stack:list lframe) (steps:nat)
  : Pure lrun (requires linv_o g m) (ensures fun r -> lrun_ok g r) (decreases steps) =
  match stack with
  | [] -> CG.lemma_cgrows_refl g; LRan g m
  | fr :: rest ->
    if steps = 0 then LStopped (CG.BuildExhausted T.Preparation)
    else match lift_frame a g m fr rest with
      | LNext g1 m1 stack1 ->
        let r = lift_loop a g1 m1 stack1 (steps - 1) in
        lemma_lrun_trans g g1 r;
        r
      | LHalt b -> LStopped b

noeq
type lifting =
  | LiftedNode : graph:CG.cgraph -> memo:lift_memo -> node:nat -> lifting
  | LiftStopped : built:CG.built -> lifting

let lift_node_ok (a c:nat) (g:CG.cgraph) (x:nat) (r:lifting) : prop =
  match r with
  | LiftedNode g' m' y -> CG.graph_inv g' /\ CG.cgrows g g' /\ memo_ok g' m' /\ lifted_in a c g' x y
  | LiftStopped b -> ~(CG.Built? b)

(* The node storing the lift of `x` with shift `a` under cutoff `c`. *)
let rec lemma_lift_zero (c:nat) (e:expr) : Lemma (ensures D.lift 0 c e == e) (decreases e) =
  match e with
  | Var _ _ -> ()
  | App _ args -> lemma_lift_args_zero c args
  | Quantifier _ bs _ b -> lemma_lift_zero (c + L.length bs) b

and lemma_lift_args_zero (c:nat) (args:list expr) : Lemma (ensures D.lift_args 0 c args == args) (decreases args) =
  match args with
  | [] -> ()
  | a :: rest -> lemma_lift_zero c a; lemma_lift_args_zero c rest

(* A lift by 0 is the node itself, without a walk. *)
let glift (a c:nat) (g:CG.cgraph{CG.graph_inv g}) (m:lift_memo{memo_ok g m}) (x:nat{x < CG.node_count g})
  : r:lifting{lift_node_ok a c g x r} =
  reveal_linv g m;
  if a = 0 then begin
    CG.lemma_cgrows_refl g;
    (match CG.value_of g x with Some v -> lemma_lift_zero c v | None -> ());
    assert (CG.node_exact g x);
    CG.reveal_exact g x;
    LiftedNode g m x
  end
  else
  match lift_loop a g m [LEnter c x] g.CG.prep with
  | LRan g' m' ->
    reveal_linv g' m';
    (match memo_get m' a c x with
     | Some y -> LiftedNode g' m' y
     | None -> LiftStopped CG.BuildInvalid)
  | LStopped b -> LiftStopped b

(* --- The instantiation of a node ------------------------------------------------------------------- *)

(* The argument node of the variable `n`: the node at the position of `n` in
   `vars`, or none (one unit per variable compared, charged by the caller). *)
let rec arg_node (n:nat) (vars:list nat) (an:list nat) : Tot (option nat) (decreases vars) =
  match vars, an with
  | v :: vs, a :: rest -> if n = v then Some a else arg_node n vs rest
  | _, _ -> None

let rec lemma_arg_node (g:CG.cgraph) (n:nat) (vars:list nat) (an:list nat) (avs:list expr)
  : Lemma (requires CS.all_below an (CG.node_count g) /\ CG.values_of g an == Some avs)
          (ensures (match arg_node n vars an with
                    | Some a -> a < CG.node_count g /\
                               (match CG.value_of g a with Some v -> D.argument n vars avs == Some v | None -> False)
                    | None -> D.argument n vars avs == None))
          (decreases vars)
  = match vars, an, avs with
    | v :: vs, a :: rest, _ :: avs' -> if n = v then () else lemma_arg_node g n vs rest avs'
    | _, _, _ -> ()

(* `y` stores in `g` the instance at binder depth `d` of what `x` stores,
   the variables `vars` replaced by the expressions of the nodes `an`. *)
let inst_in (vars an:list nat) (d:nat) (g:CG.cgraph) (x y:nat) : prop =
  x < CG.node_count g /\ y < CG.node_count g /\
  (match CG.value_of g x, CG.values_of g an, CG.value_of g y with
   | Some v, Some avs, Some w -> D.instantiate d vars avs v == Some w
   | _, _, _ -> False)

let im_ok (vars an:list nat) (g:CG.cgraph) (im:memo2) : prop =
  forall (d x:nat). (match get2 im d x with Some y -> inst_in vars an d g x y | None -> True)

let iinv (vars an:list nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) : prop =
  CG.graph_inv g /\ CS.all_below an (CG.node_count g) /\ im_ok vars an g im /\ memo_ok g lm

let lemma_inst_in_grows (vars an:list nat) (d:nat) (g g':CG.cgraph) (x y:nat)
  : Lemma (requires CG.cgrows g g' /\ CS.all_below an (CG.node_count g) /\ inst_in vars an d g x y)
          (ensures inst_in vars an d g' x y)
  = CG.lemma_values_of_grows g g' an

let lemma_iinv_grows (vars an:list nat) (g g':CG.cgraph) (im:memo2) (lm:lift_memo)
  : Lemma (requires iinv vars an g im lm /\ CG.graph_inv g' /\ CG.cgrows g g') (ensures iinv vars an g' im lm)
  = T.lemma_all_below_widen an (CG.node_count g) (CG.node_count g');
    lemma_memo_grows g g' lm;
    let aux (d x:nat) : Lemma (match get2 im d x with Some y -> inst_in vars an d g' x y | None -> True)
      = match get2 im d x with Some y -> lemma_inst_in_grows vars an d g g' x y | None -> () in
    FStar.Classical.forall_intro_2 aux

let lemma_im_extend (vars an:list nat) (g:CG.cgraph) (im:memo2) (d x y:nat)
  : Lemma (requires im_ok vars an g im /\ inst_in vars an d g x y) (ensures im_ok vars an g (put2 im d x y))
  = let aux (d' x':nat) : Lemma (match get2 (put2 im d x y) d' x' with Some y' -> inst_in vars an d' g x' y' | None -> True)
      = lemma_put2 im d x y d' x' in
    FStar.Classical.forall_intro_2 aux

let rec lemma_inst_args (vars an:list nat) (d:nat) (g:CG.cgraph) (im:memo2) (xs:list nat) (args avs:list expr)
  : Lemma (requires im_ok vars an g im /\ CG.values_of g xs == Some args /\ CG.values_of g an == Some avs)
          (ensures (match I.opt_map (get2 im d) xs with
                    | Some ys -> (match CG.values_of g ys with
                                 | Some vs -> D.instantiate_args d vars avs args == Some vs
                                 | None -> False)
                    | None -> True))
          (decreases xs)
  = match xs, args with
    | x :: xs', _ :: args' ->
      lemma_inst_args vars an d g im xs' args' avs;
      (match get2 im d x with Some y -> assert (inst_in vars an d g x y) | None -> ())
    | _, _ -> ()

type iframe =
  | IEnter : d:nat -> x:nat -> iframe
  | IExit : d:nat -> x:nat -> iframe

let rec ienters (d:nat) (xs:list nat) (tail:list iframe) : Tot (list iframe) (decreases xs) =
  match xs with
  | [] -> tail
  | x :: rest -> ienters d rest (IEnter d x :: tail)

noeq
type istep =
  | INext : graph:CG.cgraph -> im:memo2 -> lm:lift_memo -> stack:list iframe -> istep
  | IHalt : built:CG.built -> istep

let istep_ok (vars an:list nat) (g:CG.cgraph) (r:istep) : prop =
  match r with
  | INext g' im' lm' _ -> iinv vars an g' im' lm' /\ CG.cgrows g g'
  | IHalt b -> ~(CG.Built? b)

(* The instance `y` of `x` at depth `d`, recorded in the memo (its update charged). *)
let iput (vars an:list nat) (d:nat) (g0 g:CG.cgraph) (im:memo2) (lm:lift_memo) (x y:nat) (rest:list iframe)
  : Pure istep (requires iinv vars an g im lm /\ CG.cgrows g0 g /\ inst_in vars an d g x y)
               (ensures fun r -> istep_ok vars an g0 r) =
  match charge g 0 memo_units with
  | Some g1 ->
    lemma_charge g 0 memo_units;
    lemma_iinv_grows vars an g g1 im lm;
    lemma_inst_in_grows vars an d g g1 x y;
    lemma_im_extend vars an g1 im d x y;
    CG.lemma_cgrows_trans g0 g g1;
    INext g1 (put2 im d x y) lm rest
  | None -> IHalt (CG.BuildExhausted T.Storage)

let inst_var (vars an:list nat) (d:nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) (x:nat) (rest:list iframe)
  : Pure istep (requires iinv vars an g im lm /\ x < CG.node_count g /\
                         (match CG.node_of g x, CG.value_of g x with
                          | Some (T.ENVar _ _), Some (Var _ _) -> True | _, _ -> False))
               (ensures fun r -> istep_ok vars an g r) =
  CG.lemma_cgrows_refl g;
  lemma_values_some g an;
  let Some (Var n _) = CG.value_of g x in
  if n < d then iput vars an d g g im lm x x rest
  else match charge g (L.length vars) 0 with
  | None -> IHalt (CG.BuildExhausted T.Preparation)
  | Some g1 ->
    lemma_charge g (L.length vars) 0;
    lemma_iinv_grows vars an g g1 im lm;
    lemma_values_some g1 an;
    let Some avs = CG.values_of g1 an in
    lemma_arg_node g1 (n - d) vars an avs;
    match arg_node (n - d) vars an with
    | None -> IHalt CG.BuildInvalid
    | Some a ->
      (match glift d 0 g1 lm a with
       | LiftedNode g2 lm2 y ->
         lemma_iinv_grows vars an g1 g2 im lm;
         CG.lemma_values_of_grows g1 g2 an;
         CG.lemma_cgrows_trans g g1 g2;
         assert (inst_in vars an d g2 x y);
         iput vars an d g g2 im lm2 x y rest
       | LiftStopped b -> IHalt b)

let inst_enter (vars an:list nat) (d:nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) (x:nat) (rest:list iframe)
  : Pure istep (requires iinv vars an g im lm) (ensures fun r -> istep_ok vars an g r) =
  CG.lemma_cgrows_refl g;
  if x >= CG.node_count g then IHalt CG.BuildInvalid
  else match get2 im d x with
  | Some _ -> INext g im lm rest
  | None ->
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENVar _ _), Some (Var _ _) -> inst_var vars an d g im lm x rest
    | Some (T.ENApp _ xs _), Some (App _ _) ->
      (match push g (1 + L.length xs) with
       | Some g1 -> lemma_iinv_grows vars an g g1 im lm; INext g1 im lm (ienters d xs (IExit d x :: rest))
       | None -> IHalt (CG.BuildExhausted T.Storage))
    | Some (T.ENQuant _ _ y _), Some (Quantifier _ bs _ _) ->
      (match push g 2 with
       | Some g1 -> lemma_iinv_grows vars an g g1 im lm; INext g1 im lm (IEnter (d + L.length bs) y :: IExit d x :: rest)
       | None -> IHalt (CG.BuildExhausted T.Storage))
    | _, _ -> IHalt CG.BuildInvalid

let inst_exit_app (vars an:list nat) (d:nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) (x:nat) (xs:list nat) (rest:list iframe)
  : Pure istep (requires iinv vars an g im lm /\ x < CG.node_count g /\
                         (match CG.node_of g x, CG.value_of g x with
                          | Some (T.ENApp _ xs' _), Some (App _ _) -> xs' == xs
                          | _, _ -> False))
               (ensures fun r -> istep_ok vars an g r) =
  match charge g (L.length xs * CS.table_units) 0 with
  | None -> IHalt (CG.BuildExhausted T.Preparation)
  | Some g1 ->
    lemma_charge g (L.length xs * CS.table_units) 0;
    lemma_iinv_grows vars an g g1 im lm;
    assert (CG.node_exact g1 x);
    CG.reveal_exact g1 x;
    opt_map_tail_is (get2 im d) xs;
    let Some (App f args) = CG.value_of g1 x in
    lemma_values_some g1 an;
    let Some avs = CG.values_of g1 an in
    lemma_inst_args vars an d g1 im xs args avs;
    match I.opt_map_tail (get2 im d) xs with
    | None -> IHalt CG.BuildInvalid
    | Some ys ->
      CS.lemma_same_ids ys xs;
      if CS.same_ids ys xs then iput vars an d g g1 im lm x x rest
      else begin
        lemma_rebuild_app g1 x ys;
        match rebuild_app g1 x ys with
        | CG.Built g2 y ->
          lemma_iinv_grows vars an g1 g2 im lm;
          CG.lemma_values_of_grows g1 g2 an;
          CG.lemma_cgrows_trans g g1 g2;
          assert (inst_in vars an d g2 x y);
          iput vars an d g g2 im lm x y rest
        | CG.BuildExhausted p -> IHalt (CG.BuildExhausted p)
        | CG.BuildInvalid -> IHalt CG.BuildInvalid
      end

let inst_exit_quant (vars an:list nat) (d:nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) (x y n:nat) (rest:list iframe)
  : Pure istep (requires iinv vars an g im lm /\ x < CG.node_count g /\
                         (match CG.node_of g x, CG.value_of g x with
                          | Some (T.ENQuant _ _ y' _), Some (Quantifier _ bs _ _) -> y' == y /\ n == L.length bs
                          | _, _ -> False))
               (ensures fun r -> istep_ok vars an g r) =
  CG.lemma_cgrows_refl g;
  assert (CG.node_exact g x);
  CG.reveal_exact g x;
  match get2 im (d + n) y with
  | None -> IHalt CG.BuildInvalid
  | Some z ->
    assert (inst_in vars an (d + n) g y z);
    if z = y then iput vars an d g g im lm x x rest
    else begin
      lemma_rebuild_quant g x z;
      match rebuild_quant g x z with
      | CG.Built g2 w ->
        lemma_iinv_grows vars an g g2 im lm;
        CG.lemma_values_of_grows g g2 an;
        assert (inst_in vars an d g2 x w);
        iput vars an d g g2 im lm x w rest
      | CG.BuildExhausted p -> IHalt (CG.BuildExhausted p)
      | CG.BuildInvalid -> IHalt CG.BuildInvalid
    end

let inst_exit (vars an:list nat) (d:nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) (x:nat) (rest:list iframe)
  : Pure istep (requires iinv vars an g im lm) (ensures fun r -> istep_ok vars an g r) =
  CG.lemma_cgrows_refl g;
  if x >= CG.node_count g then IHalt CG.BuildInvalid
  else match get2 im d x with
  | Some _ -> INext g im lm rest
  | None ->
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENApp _ xs _), Some (App _ _) -> inst_exit_app vars an d g im lm x xs rest
    | Some (T.ENQuant _ _ y _), Some (Quantifier _ bs _ _) -> inst_exit_quant vars an d g im lm x y (L.length bs) rest
    | _, _ -> IHalt CG.BuildInvalid

let inst_frame (vars an:list nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) (fr:iframe) (rest:list iframe)
  : Pure istep (requires iinv vars an g im lm) (ensures fun r -> istep_ok vars an g r) =
  match charge g memo_units 0 with
  | None -> IHalt (CG.BuildExhausted T.Preparation)
  | Some g0 ->
    lemma_charge g memo_units 0;
    lemma_iinv_grows vars an g g0 im lm;
    let s = match fr with IEnter d x -> inst_enter vars an d g0 im lm x rest | IExit d x -> inst_exit vars an d g0 im lm x rest in
    (match s with INext g1 _ _ _ -> CG.lemma_cgrows_trans g g0 g1 | _ -> ());
    s

(* The loop's invariant, opaque to the solver: the loop only passes it on. *)
[@@"opaque_to_smt"]
let iinv_o (vars an:list nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) : prop = iinv vars an g im lm

let reveal_iinv (vars an:list nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo)
  : Lemma (iinv_o vars an g im lm <==> iinv vars an g im lm)
  = FStar.Pervasives.reveal_opaque (`%iinv_o) (iinv_o vars an g im lm)

noeq
type irun =
  | IRan : graph:CG.cgraph -> im:memo2 -> lm:lift_memo -> irun
  | IStopped : built:CG.built -> irun

let irun_ok (vars an:list nat) (g:CG.cgraph) (r:irun) : prop =
  match r with
  | IRan g' im' lm' -> iinv_o vars an g' im' lm' /\ CG.cgrows g g'
  | IStopped b -> ~(CG.Built? b)

let istep_ok_o (vars an:list nat) (g:CG.cgraph) (r:istep) : prop =
  match r with
  | INext g' im' lm' _ -> iinv_o vars an g' im' lm' /\ CG.cgrows g g'
  | IHalt b -> ~(CG.Built? b)

let inst_frame_o (vars an:list nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) (fr:iframe) (rest:list iframe)
  : Pure istep (requires iinv_o vars an g im lm) (ensures fun r -> istep_ok_o vars an g r) =
  reveal_iinv vars an g im lm;
  let r = inst_frame vars an g im lm fr rest in
  (match r with INext g' im' lm' _ -> reveal_iinv vars an g' im' lm' | _ -> ());
  r

let lemma_irun_trans (vars an:list nat) (g g1:CG.cgraph) (r:irun)
  : Lemma (requires CG.cgrows g g1 /\ irun_ok vars an g1 r) (ensures irun_ok vars an g r)
  = match r with IRan g2 _ _ -> CG.lemma_cgrows_trans g g1 g2 | _ -> ()

let rec inst_loop (vars an:list nat) (g:CG.cgraph) (im:memo2) (lm:lift_memo) (stack:list iframe) (steps:nat)
  : Pure irun (requires iinv_o vars an g im lm) (ensures fun r -> irun_ok vars an g r) (decreases steps) =
  match stack with
  | [] -> CG.lemma_cgrows_refl g; IRan g im lm
  | fr :: rest ->
    if steps = 0 then IStopped (CG.BuildExhausted T.Preparation)
    else match inst_frame_o vars an g im lm fr rest with
      | INext g1 im1 lm1 stack1 ->
        let r = inst_loop vars an g1 im1 lm1 stack1 (steps - 1) in
        lemma_irun_trans vars an g g1 r;
        r
      | IHalt b -> IStopped b

noeq
type inst_result =
  | InstNode : graph:CG.cgraph -> node:nat -> inst_result
  | InstStopped : built:CG.built -> inst_result

(* The node storing the instance of `x` (`D.instantiate 0 vars avs`), `avs`
   the expressions of the argument nodes `an`. *)
let ginst (vars an:list nat) (g:CG.cgraph) (x:nat)
  : Pure inst_result (requires CG.graph_inv g /\ CS.all_below an (CG.node_count g) /\ x < CG.node_count g)
                  (ensures fun r -> match r with
                                 | InstNode g' z -> CG.graph_inv g' /\ CG.cgrows g g' /\ inst_in vars an 0 g' x z
                                 | InstStopped b -> ~(CG.Built? b)) =
  assert (im_ok vars an g I.Empty);
  assert (memo_ok g I.Empty);
  reveal_iinv vars an g I.Empty I.Empty;
  match inst_loop vars an g I.Empty I.Empty [IEnter 0 x] g.CG.prep with
  | IRan g' im' lm' ->
    reveal_iinv vars an g' im' lm';
    (match get2 im' 0 x with
     | Some z -> InstNode g' z
     | None -> InstStopped CG.BuildInvalid)
  | IStopped b -> InstStopped b

(* --- Interning an expression ------------------------------------------------------------------------ *)

(* A definition's body is an expression of the document, not a node: it is
   interned bottom-up over a worklist. Each subexpression gets an index `k`
   (`sub`), its children consecutive fresh indices (`assign`); its node
   (`res`) is built when its children's are. The sorts of a variable, of a
   declaration and of a quantifier are interned (their names counted by the
   bounded counter). A quantifier whose sort is not its kind's over its body
   is not interned (`BuildInvalid`). *)

let intern_sort_in (g:CG.cgraph) (s:sort) : CG.sorted =
  match T.intern_sort g.CG.terms.T.sorts s g.CG.prep g.CG.store with
  | T.SortInterned t c w st -> CG.Sorted (CG.with_sorts g t w st) (s, c)
  | T.SortExhausted p -> CG.SortExhausted p

let lemma_intern_sort_in (g:CG.cgraph) (s:sort)
  : Lemma (requires CG.graph_inv g)
          (ensures (match intern_sort_in g s with
                    | CG.Sorted g' c -> CG.graph_inv g' /\ CG.cgrows g g' /\ CG.csort_ok g' c /\ fst c == s /\
                                       CG.node_count g' == CG.node_count g
                    | CG.SortExhausted _ -> True))
  = T.lemma_intern_sort g.CG.terms.T.sorts s g.CG.prep g.CG.store;
    match T.intern_sort g.CG.terms.T.sorts s g.CG.prep g.CG.store with
    | T.SortInterned t c w st -> CG.lemma_with_sorts g t w st
    | _ -> ()

noeq
type sorted_ids =
  | SortIds : graph:CG.cgraph -> ids:list nat -> sorted_ids
  | SortIdsExhausted : phase:T.phase -> sorted_ids

let intern_sorts_in (g:CG.cgraph) (ss:list sort) : sorted_ids =
  match T.intern_sorts g.CG.terms.T.sorts ss g.CG.prep g.CG.store with
  | T.SortsInterned t ids _ w st -> SortIds (CG.with_sorts g t w st) ids
  | T.SortsExhausted p -> SortIdsExhausted p

let lemma_intern_sorts_in (g:CG.cgraph) (ss:list sort)
  : Lemma (requires CG.graph_inv g)
          (ensures (match intern_sorts_in g ss with
                    | SortIds g' ids -> CG.graph_inv g' /\ CG.cgrows g g' /\ CS.all_below ids (CG.sort_count g') /\
                                       L.map (CG.interp g') ids == ss /\ CG.node_count g' == CG.node_count g
                    | SortIdsExhausted _ -> True))
  = T.lemma_intern_sorts g.CG.terms.T.sorts ss g.CG.prep g.CG.store;
    match T.intern_sorts g.CG.terms.T.sorts ss g.CG.prep g.CG.store with
    | T.SortsInterned t _ _ w st -> CG.lemma_with_sorts g t w st
    | _ -> ()

noeq
type tstate = { tg: CG.cgraph; sub: I.index_tree expr; res: I.index_tree nat; next: nat }

type tframe =
  | TEnter : k:nat -> tframe
  | TExit : k:nat -> ks:list nat -> tframe

let sub_below (sub:I.index_tree expr) (n:nat) : prop =
  forall (k:nat). Some? (I.index_get sub k) ==> k < n

let res_ok (g:CG.cgraph) (sub:I.index_tree expr) (res:I.index_tree nat) : prop =
  forall (k:nat). (match I.index_get res k with
                   | Some y -> (match I.index_get sub k with
                               | Some t -> y < CG.node_count g /\ CG.value_of g y == Some t
                               | None -> False)
                   | None -> True)

let rec laid (sub:I.index_tree expr) (ks:list nat) (es:list expr) : Tot prop (decreases ks) =
  match ks, es with
  | [], [] -> True
  | k :: ks', e :: es' -> I.index_get sub k == Some e /\ laid sub ks' es'
  | _, _ -> False

let children_laid (sub:I.index_tree expr) (t:expr) (ks:list nat) : prop =
  match t with
  | App _ es -> laid sub ks es
  | Quantifier _ _ _ b -> laid sub ks [b]
  | Var _ _ -> False

let tframe_ok (st:tstate) (fr:tframe) : prop =
  match fr with
  | TExit k ks -> CS.all_below ks st.next /\
                 (match I.index_get st.sub k with Some t -> children_laid st.sub t ks | None -> False)
  | TEnter _ -> True

let rec tstack_ok (st:tstate) (stack:list tframe) : Tot prop (decreases stack) =
  match stack with
  | [] -> True
  | fr :: rest -> tframe_ok st fr /\ tstack_ok st rest

let tinv (st:tstate) (stack:list tframe) : prop =
  CG.graph_inv st.tg /\ sub_below st.sub st.next /\ res_ok st.tg st.sub st.res /\ tstack_ok st stack

(* `sub'` keeps every index of `sub` below `n`. *)
let agree_below (sub sub':I.index_tree expr) (n:nat) : prop =
  forall (k:nat). k < n ==> I.index_get sub' k == I.index_get sub k

let rec lemma_laid_agree (sub sub':I.index_tree expr) (n:nat) (ks:list nat) (es:list expr)
  : Lemma (requires agree_below sub sub' n /\ CS.all_below ks n /\ laid sub ks es) (ensures laid sub' ks es)
          (decreases ks)
  = match ks, es with
    | _ :: ks', _ :: es' -> lemma_laid_agree sub sub' n ks' es'
    | _, _ -> ()

let rec lemma_tstack_grows (st st':tstate) (stack:list tframe)
  : Lemma (requires tstack_ok st stack /\ st.next <= st'.next /\ agree_below st.sub st'.sub st.next /\ sub_below st.sub st.next)
          (ensures tstack_ok st' stack) (decreases stack)
  = match stack with
    | [] -> ()
    | TEnter _ :: rest -> lemma_tstack_grows st st' rest
    | TExit k ks :: rest ->
      T.lemma_all_below_widen ks st.next st'.next;
      (match I.index_get st.sub k with
       | Some (App _ es) -> lemma_laid_agree st.sub st'.sub st.next ks es
       | Some (Quantifier _ _ _ b) -> lemma_laid_agree st.sub st'.sub st.next ks [b]
       | _ -> ());
      lemma_tstack_grows st st' rest

let rec range (n m:nat) : Tot (list nat) (decreases m) = if m = 0 then [] else n :: range (n + 1) (m - 1)

(* Fresh indices `next`, `next + 1`, ... for `es`, last first in `acc`. *)
let rec assign (sub:I.index_tree expr) (next:nat) (es:list expr) (acc:list nat)
  : Tot (I.index_tree expr & nat & list nat) (decreases es) =
  match es with
  | [] -> (sub, next, acc)
  | e :: rest -> assign (I.index_put sub next e) (next + 1) rest (next :: acc)

let rec lemma_laid_append (sub:I.index_tree expr) (k1 k2:list nat) (e1 e2:list expr)
  : Lemma (requires laid sub k1 e1 /\ laid sub k2 e2) (ensures laid sub (L.append k1 k2) (L.append e1 e2)) (decreases k1)
  = match k1, e1 with
    | _ :: k1', _ :: e1' -> lemma_laid_append sub k1' k2 e1' e2
    | _, _ -> ()

let rec lemma_all_below_append (a b:list nat) (n:nat)
  : Lemma (requires CS.all_below a n /\ CS.all_below b n) (ensures CS.all_below (L.append a b) n) (decreases a)
  = match a with [] -> () | _ :: a' -> lemma_all_below_append a' b n

let rec lemma_assign (sub:I.index_tree expr) (next:nat) (es:list expr) (acc:list nat) (prefix:list expr)
  : Lemma (requires sub_below sub next /\ CS.all_below acc next /\ laid sub (L.rev acc) prefix)
          (ensures (let (sub', next', acc') = assign sub next es acc in
                    next' == next + L.length es /\ sub_below sub' next' /\ agree_below sub sub' next /\
                    CS.all_below acc' next' /\ laid sub' (L.rev acc') (L.append prefix es)))
          (decreases es)
  = match es with
    | [] -> L.append_l_nil prefix
    | e :: rest ->
      let sub1 = I.index_put sub next e in
      let aux (k:nat) : Lemma (I.index_get sub1 k == (if k = next then Some e else I.index_get sub k))
        = I.lemma_index_put sub next e k in
      FStar.Classical.forall_intro aux;
      assert (agree_below sub sub1 next);
      T.lemma_all_below_rev acc next;
      lemma_laid_agree sub sub1 next (L.rev acc) prefix;
      T.lemma_all_below_widen acc next (next + 1);
      Z3List.lemma_rev_cons next acc;
      lemma_laid_append sub1 (L.rev acc) [next] prefix [e];
      L.append_assoc prefix [e] rest;
      lemma_assign sub1 (next + 1) rest (next :: acc) (L.append prefix [e]);
      let (sub', _, _) = assign sub1 (next + 1) rest (next :: acc) in
      assert (agree_below sub1 sub' (next + 1));
      assert (agree_below sub sub' next)

let rec lemma_res_laid (g:CG.cgraph) (sub:I.index_tree expr) (res:I.index_tree nat) (ks:list nat) (es:list expr)
  : Lemma (requires res_ok g sub res /\ laid sub ks es)
          (ensures (match I.opt_map (I.index_get res) ks with
                    | Some ys -> CS.all_below ys (CG.node_count g) /\ CG.values_of g ys == Some es
                    | None -> True))
          (decreases ks)
  = match ks, es with
    | k :: ks', _ :: es' -> lemma_res_laid g sub res ks' es'
    | _, _ -> ()

let rec tenters (ks:list nat) (tail:list tframe) : Tot (list tframe) (decreases ks) =
  match ks with
  | [] -> tail
  | k :: rest -> tenters rest (TEnter k :: tail)

let rec lemma_tenters (st:tstate) (ks:list nat) (tail:list tframe)
  : Lemma (requires tstack_ok st tail) (ensures tstack_ok st (tenters ks tail)) (decreases ks)
  = match ks with [] -> () | k :: rest -> lemma_tenters st rest (TEnter k :: tail)

noeq
type tstep =
  | TNext : st:tstate -> stack:list tframe -> tstep
  | THalt : built:CG.built -> tstep

let tgrows (st st':tstate) : prop =
  CG.cgrows st.tg st'.tg /\ st.next <= st'.next /\ agree_below st.sub st'.sub st.next

let tstep_ok (st:tstate) (r:tstep) : prop =
  match r with
  | TNext st' stack' -> tinv st' stack' /\ tgrows st st'
  | THalt b -> ~(CG.Built? b)

let lemma_res_grows (g g':CG.cgraph) (sub sub':I.index_tree expr) (n:nat) (res:I.index_tree nat)
  : Lemma (requires res_ok g sub res /\ CG.cgrows g g' /\ sub_below sub n /\ agree_below sub sub' n)
          (ensures res_ok g' sub' res)
  = ()

let lemma_res_extend (g:CG.cgraph) (sub:I.index_tree expr) (res:I.index_tree nat) (k y:nat)
  : Lemma (requires res_ok g sub res /\ y < CG.node_count g /\
                    (match I.index_get sub k with Some t -> CG.value_of g y == Some t | None -> False))
          (ensures res_ok g sub (I.index_put res k y))
  = let aux (j:nat) : Lemma (match I.index_get (I.index_put res k y) j with
                             | Some y' -> (match I.index_get sub j with
                                          | Some t -> y' < CG.node_count g /\ CG.value_of g y' == Some t
                                          | None -> False)
                             | None -> True)
      = I.lemma_index_put res k y j in
    FStar.Classical.forall_intro aux

let lemma_agree_refl (sub:I.index_tree expr) (n:nat) : Lemma (agree_below sub sub n) = ()

(* The node `y` of index `k`, recorded (its update charged). *)
let tres (st:tstate) (g':CG.cgraph) (k y:nat) (rest:list tframe)
  : Pure tstep (requires tinv st rest /\ CG.graph_inv g' /\ CG.cgrows st.tg g' /\ y < CG.node_count g' /\
                         (match I.index_get st.sub k with Some t -> CG.value_of g' y == Some t | None -> False))
               (ensures fun r -> tstep_ok st r) =
  match charge g' 0 (1 + CS.table_units) with
  | None -> THalt (CG.BuildExhausted T.Storage)
  | Some g1 ->
    lemma_charge g' 0 (1 + CS.table_units);
    CG.lemma_cgrows_trans st.tg g' g1;
    assert (CG.value_of g1 y == CG.value_of g' y);
    lemma_res_grows st.tg g1 st.sub st.sub st.next st.res;
    lemma_res_extend g1 st.sub st.res k y;
    let st' = { st with tg = g1; res = I.index_put st.res k y } in
    lemma_agree_refl st.sub st.next;
    lemma_tstack_grows st st' rest;
    assert (CG.graph_inv st'.tg);
    assert (sub_below st'.sub st'.next);
    assert (res_ok st'.tg st'.sub st'.res);
    assert (tstack_ok st' rest);
    assert (tinv st' rest);
    assert (tgrows st st');
    TNext st' rest

let intern_var (st:tstate) (k:nat) (n:nat) (s:sort) (rest:list tframe)
  : Pure tstep (requires tinv st rest /\ I.index_get st.sub k == Some (Var n s)) (ensures fun r -> tstep_ok st r) =
  lemma_intern_sort_in st.tg s;
  match intern_sort_in st.tg s with
  | CG.SortExhausted p -> THalt (CG.BuildExhausted p)
  | CG.Sorted g1 c ->
    CG.lemma_add_var g1 n c;
    match CG.add_var g1 n c with
    | CG.Built g2 y -> CG.lemma_cgrows_trans st.tg g1 g2; tres st g2 k y rest
    | CG.BuildExhausted p -> THalt (CG.BuildExhausted p)
    | CG.BuildInvalid -> THalt CG.BuildInvalid

let intern_open (st:tstate) (k:nat) (es:list expr) (t:expr) (rest:list tframe)
  : Pure tstep (requires tinv st rest /\ I.index_get st.sub k == Some t /\
                         (match t with App _ es' -> es' == es | Quantifier _ _ _ b -> es == [b] | Var _ _ -> False))
               (ensures fun r -> tstep_ok st r) =
  let m = L.length es in
  FStar.Math.Lemmas.nat_times_nat_is_nat m CS.table_units;
  FStar.Math.Lemmas.nat_times_nat_is_nat m (2 + CS.table_units);
  let cp : nat = m * CS.table_units in
  let cs : nat = 1 + m * (2 + CS.table_units) in
  match charge st.tg cp cs with
  | None -> THalt (CG.BuildExhausted T.Storage)
  | Some g1 ->
    lemma_charge st.tg cp cs;
    lemma_assign st.sub st.next es [] [];
    let (sub', next', acc) = assign st.sub st.next es [] in
    let ks = L.rev acc in
    T.lemma_all_below_rev acc next';
    let st' = { st with tg = g1; sub = sub'; next = next' } in
    lemma_res_grows st.tg g1 st.sub sub' st.next st.res;
    lemma_tstack_grows st st' rest;
    assert (I.index_get sub' k == Some t);
    assert (tframe_ok st' (TExit k ks));
    lemma_tenters st' ks (TExit k ks :: rest);
    assert (CG.graph_inv st'.tg);
    assert (sub_below st'.sub st'.next);
    assert (res_ok st'.tg st'.sub st'.res);
    assert (tstack_ok st' (tenters ks (TExit k ks :: rest)));
    assert (tinv st' (tenters ks (TExit k ks :: rest)));
    assert (tgrows st st');
    TNext st' (tenters ks (TExit k ks :: rest))

let intern_enter (st:tstate) (k:nat) (rest:list tframe)
  : Pure tstep (requires tinv st rest) (ensures fun r -> tstep_ok st r) =
  match I.index_get st.sub k with
  | None -> THalt CG.BuildInvalid
  | Some t ->
    match t with
    | Var n s -> intern_var st k n s rest
    | App _ es -> intern_open st k es t rest
    | Quantifier _ _ _ b -> intern_open st k [b] t rest

let intern_close_app (st:tstate) (k:nat) (f:func_decl) (es:list expr) (ys:list nat) (rest:list tframe)
  : Pure tstep (requires tinv st rest /\ I.index_get st.sub k == Some (App f es) /\
                         CS.all_below ys (CG.node_count st.tg) /\ CG.values_of st.tg ys == Some es)
               (ensures fun r -> tstep_ok st r) =
  lemma_intern_sort_in st.tg f.range;
  match intern_sort_in st.tg f.range with
  | CG.SortExhausted p -> THalt (CG.BuildExhausted p)
  | CG.Sorted g1 r ->
    lemma_intern_sorts_in g1 f.domain;
    match intern_sorts_in g1 f.domain with
    | SortIdsExhausted p -> THalt (CG.BuildExhausted p)
    | SortIds g2 dom ->
      CG.lemma_csort_grows g1 g2 r;
      CG.lemma_cgrows_trans st.tg g1 g2;
      CG.lemma_values_of_grows st.tg g2 ys;
      let d = { CG.decl = f; CG.dom = dom; CG.rng = snd r } in
      assert (CG.decl_ok g2 d);
      CG.lemma_add_app g2 d ys;
      match CG.add_app g2 d ys with
      | CG.Built g3 y -> CG.lemma_cgrows_trans st.tg g2 g3; tres st g3 k y rest
      | CG.BuildExhausted p -> THalt (CG.BuildExhausted p)
      | CG.BuildInvalid -> THalt CG.BuildInvalid

let intern_close_quant (st:tstate) (k:nat) (qk:quantifier_kind) (bs:list sort) (q:sort) (b:expr) (z:nat) (rest:list tframe)
  : Pure tstep (requires tinv st rest /\ I.index_get st.sub k == Some (Quantifier qk bs q b) /\
                         z < CG.node_count st.tg /\ CG.value_of st.tg z == Some b)
               (ensures fun r -> tstep_ok st r) =
  lemma_intern_sorts_in st.tg bs;
  match intern_sorts_in st.tg bs with
  | SortIdsExhausted p -> THalt (CG.BuildExhausted p)
  | SortIds g1 ids ->
    lemma_pair_sorts g1 bs ids;
    CG.lemma_add_quant g1 qk (pair_sorts bs ids) z;
    match CG.add_quant g1 qk (pair_sorts bs ids) z with
    | CG.BuildExhausted p -> THalt (CG.BuildExhausted p)
    | CG.BuildInvalid -> THalt CG.BuildInvalid
    | CG.Built g2 w ->
      lemma_intern_sort_in g2 q;
      match intern_sort_in g2 q with
      | CG.SortExhausted p -> THalt (CG.BuildExhausted p)
      | CG.Sorted g3 c ->
        CG.lemma_node_sort g3 w;
        (match CG.node_of g3 w with
         | Some n ->
           if CG.enode_sort n = snd c then begin
             CG.lemma_cgrows_trans st.tg g1 g2;
             CG.lemma_cgrows_trans st.tg g2 g3;
             tres st g3 k w rest
           end
           else THalt CG.BuildInvalid
         | None -> THalt CG.BuildInvalid)

let lemma_single (g:CG.cgraph) (z:nat) (b:expr)
  : Lemma (requires CS.all_below [z] (CG.node_count g) /\ CG.values_of g [z] == Some [b])
          (ensures z < CG.node_count g /\ CG.value_of g z == Some b)
  = ()

let intern_exit (st:tstate) (k:nat) (ks:list nat) (rest:list tframe)
  : Pure tstep (requires tinv st (TExit k ks :: rest)) (ensures fun r -> tstep_ok st r) =
  match I.index_get st.sub k with
  | None -> THalt CG.BuildInvalid
  | Some t ->
    FStar.Math.Lemmas.nat_times_nat_is_nat (L.length ks) CS.table_units;
    let cp : nat = L.length ks * CS.table_units in
    match charge st.tg cp 0 with
    | None -> THalt (CG.BuildExhausted T.Preparation)
    | Some g1 ->
      lemma_charge st.tg cp 0;
      let st1 = { st with tg = g1 } in
      lemma_res_grows st.tg g1 st.sub st.sub st.next st.res;
      lemma_tstack_grows st st1 (TExit k ks :: rest);
      opt_map_tail_is (I.index_get st.res) ks;
      match t, I.opt_map_tail (I.index_get st.res) ks with
      | App f es, Some ys ->
        lemma_res_laid g1 st.sub st.res ks es;
        let r = intern_close_app st1 k f es ys rest in
        (match r with TNext st' _ -> CG.lemma_cgrows_trans st.tg g1 st'.tg | _ -> ());
        r
      | Quantifier qk bs q b, Some [z] ->
        lemma_res_laid g1 st.sub st.res ks [b];
        lemma_single g1 z b;
        let r = intern_close_quant st1 k qk bs q b z rest in
        (match r with TNext st' _ -> CG.lemma_cgrows_trans st.tg g1 st'.tg | _ -> ());
        r
      | _, _ -> THalt CG.BuildInvalid

[@@"opaque_to_smt"]
let tinv_o (st:tstate) (stack:list tframe) : prop = tinv st stack

let reveal_tinv (st:tstate) (stack:list tframe) : Lemma (tinv_o st stack <==> tinv st stack)
  = FStar.Pervasives.reveal_opaque (`%tinv_o) (tinv_o st stack)

let tstep_ok_o (st:tstate) (r:tstep) : prop =
  match r with
  | TNext st' stack' -> tinv_o st' stack' /\ tgrows st st'
  | THalt b -> ~(CG.Built? b)

let intern_frame (st:tstate) (fr:tframe) (rest:list tframe)
  : Pure tstep (requires tinv_o st (fr :: rest)) (ensures fun r -> tstep_ok_o st r) =
  reveal_tinv st (fr :: rest);
  let r =
    match charge st.tg memo_units 0 with
    | None -> THalt (CG.BuildExhausted T.Preparation)
    | Some g0 ->
      lemma_charge st.tg memo_units 0;
      let st0 = { st with tg = g0 } in
      lemma_res_grows st.tg g0 st.sub st.sub st.next st.res;
      lemma_tstack_grows st st0 (fr :: rest);
      let r = match fr with
        | TEnter k -> intern_enter st0 k rest
        | TExit k ks -> intern_exit st0 k ks rest in
      (match r with TNext st' _ -> CG.lemma_cgrows_trans st.tg g0 st'.tg | _ -> ());
      r in
  (match r with TNext st' stack' -> reveal_tinv st' stack' | _ -> ());
  r

noeq
type trun =
  | TRan : st:tstate -> trun
  | TStopped : built:CG.built -> trun

let trun_ok (st:tstate) (r:trun) : prop =
  match r with
  | TRan st' -> tinv_o st' [] /\ tgrows st st'
  | TStopped b -> ~(CG.Built? b)

let lemma_trun_trans (st st1:tstate) (r:trun)
  : Lemma (requires tgrows st st1 /\ trun_ok st1 r) (ensures trun_ok st r)
  = match r with TRan st2 -> CG.lemma_cgrows_trans st.tg st1.tg st2.tg | _ -> ()

let rec intern_loop (st:tstate) (stack:list tframe) (steps:nat)
  : Pure trun (requires tinv_o st stack) (ensures fun r -> trun_ok st r) (decreases steps) =
  match stack with
  | [] -> CG.lemma_cgrows_refl st.tg; TRan st
  | fr :: rest ->
    if steps = 0 then TStopped (CG.BuildExhausted T.Preparation)
    else match intern_frame st fr rest with
      | TNext st1 stack1 ->
        let r = intern_loop st1 stack1 (steps - 1) in
        lemma_trun_trans st st1 r;
        r
      | THalt b -> TStopped b

noeq
type interned =
  | Interned : graph:CG.cgraph -> node:nat -> interned
  | InternStopped : built:CG.built -> interned

(* A node storing exactly the expression `e`. *)
let intern_expr (g:CG.cgraph) (e:expr)
  : Pure interned (requires CG.graph_inv g)
                  (ensures fun r -> match r with
                                 | Interned g' y -> CG.graph_inv g' /\ CG.cgrows g g' /\ y < CG.node_count g' /\
                                                   CG.value_of g' y == Some e
                                 | InternStopped b -> ~(CG.Built? b)) =
  let sub = I.index_put I.Empty 0 e in
  let aux (k:nat) : Lemma (I.index_get sub k == (if k = 0 then Some e else None)) = I.lemma_index_put I.Empty 0 e k in
  FStar.Classical.forall_intro aux;
  let st = { tg = g; sub = sub; res = I.Empty; next = 1 } in
  assert (tinv st [TEnter 0]);
  reveal_tinv st [TEnter 0];
  match intern_loop st [TEnter 0] g.CG.prep with
  | TRan st' ->
    reveal_tinv st' [];
    (match I.index_get st'.res 0 with
     | Some y -> Interned st'.tg y
     | None -> InternStopped CG.BuildInvalid)
  | TStopped b -> InternStopped b

(* --- The expansion of a node ------------------------------------------------------------------------ *)

(* The first definition of the declaration `f` and its position, as
   `D.lookup` finds it (one unit per definition compared, charged by the caller). *)
let rec find_def (defs:list D.definition) (f:func_decl) (i:nat) : Tot (option (nat & D.definition)) (decreases defs) =
  match defs with
  | [] -> None
  | d :: rest -> if d.D.symbol = f then Some (i, d) else find_def rest f (i + 1)

let rec lemma_find_def (defs:list D.definition) (f:func_decl) (i:nat)
  : Lemma (ensures (match find_def defs f i with
                    | Some (j, d) -> i <= j /\ j - i < L.length defs /\ L.index defs (j - i) == d /\ D.lookup defs f == Some d
                    | None -> D.lookup defs f == None))
          (decreases defs)
  = match defs with
    | [] -> ()
    | d :: rest -> if d.D.symbol = f then () else lemma_find_def rest f (i + 1)

(* `y` stores in `g` the expansion with fuel `f` of what `x` stores. *)
let exp_in (defs:list D.definition) (f:nat) (g:CG.cgraph) (x y:nat) : prop =
  x < CG.node_count g /\ y < CG.node_count g /\
  (match CG.value_of g x, CG.value_of g y with
   | Some v, Some w -> D.expand f defs v == Some w
   | _, _ -> False)

let em_ok (defs:list D.definition) (g:CG.cgraph) (em:memo2) : prop =
  forall (f x:nat). (match get2 em f x with Some y -> exp_in defs f g x y | None -> True)

(* The nodes of the definitions' bodies interned so far, by position. *)
let bodies_ok (defs:list D.definition) (g:CG.cgraph) (bodies:I.index_tree nat) : prop =
  forall (i:nat). (match I.index_get bodies i with
                   | Some b -> i < L.length defs /\ b < CG.node_count g /\ CG.value_of g b == Some (L.index defs i).D.body
                   | None -> True)

type eframe =
  | EEnter : f:nat -> x:nat -> eframe
  | EExit : f:nat -> x:nat -> eframe
  | EThen : f:nat -> x:nat -> z:nat -> eframe

(* The frame that expands the instance `z` of a definition at `x` carries
   the equation that makes its result `x`'s. *)
let frame_ok (defs:list D.definition) (g:CG.cgraph) (fr:eframe) : prop =
  match fr with
  | EThen f x z ->
    f > 0 /\ x < CG.node_count g /\ z < CG.node_count g /\
    (match CG.value_of g x, CG.value_of g z with
     | Some vx, Some vz -> D.expand f defs vx == D.expand (f - 1) defs vz
     | _, _ -> False)
  | _ -> True

let rec stack_ok (defs:list D.definition) (g:CG.cgraph) (st:list eframe) : Tot prop (decreases st) =
  match st with
  | [] -> True
  | fr :: rest -> frame_ok defs g fr /\ stack_ok defs g rest

let einv (defs:list D.definition) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (st:list eframe) : prop =
  CG.graph_inv g /\ em_ok defs g em /\ bodies_ok defs g bodies /\ stack_ok defs g st

let rec lemma_stack_grows (defs:list D.definition) (g g':CG.cgraph) (st:list eframe)
  : Lemma (requires CG.cgrows g g' /\ stack_ok defs g st) (ensures stack_ok defs g' st) (decreases st)
  = match st with [] -> () | _ :: rest -> lemma_stack_grows defs g g' rest

let lemma_exp_in_grows (defs:list D.definition) (f:nat) (g g':CG.cgraph) (x y:nat)
  : Lemma (requires CG.cgrows g g' /\ exp_in defs f g x y) (ensures exp_in defs f g' x y)
  = ()

let lemma_em_grows (defs:list D.definition) (g g':CG.cgraph) (em:memo2)
  : Lemma (requires CG.cgrows g g' /\ em_ok defs g em) (ensures em_ok defs g' em)
  = let aux (f x:nat) : Lemma (match get2 em f x with Some y -> exp_in defs f g' x y | None -> True)
      = match get2 em f x with Some y -> lemma_exp_in_grows defs f g g' x y | None -> () in
    FStar.Classical.forall_intro_2 aux

let lemma_bodies_grows (defs:list D.definition) (g g':CG.cgraph) (bodies:I.index_tree nat)
  : Lemma (requires CG.cgrows g g' /\ bodies_ok defs g bodies) (ensures bodies_ok defs g' bodies)
  = let aux (i:nat) : Lemma (match I.index_get bodies i with
                             | Some b -> i < L.length defs /\ b < CG.node_count g' /\ CG.value_of g' b == Some (L.index defs i).D.body
                             | None -> True)
      = () in
    FStar.Classical.forall_intro aux

let lemma_einv_grows (defs:list D.definition) (g g':CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (st:list eframe)
  : Lemma (requires einv defs g em bodies st /\ CG.graph_inv g' /\ CG.cgrows g g') (ensures einv defs g' em bodies st)
  = lemma_stack_grows defs g g' st;
    lemma_em_grows defs g g' em;
    lemma_bodies_grows defs g g' bodies
let lemma_em_extend (defs:list D.definition) (g:CG.cgraph) (em:memo2) (f x y:nat)
  : Lemma (requires em_ok defs g em /\ exp_in defs f g x y) (ensures em_ok defs g (put2 em f x y))
  = let aux (f' x':nat) : Lemma (match get2 (put2 em f x y) f' x' with Some y' -> exp_in defs f' g x' y' | None -> True)
      = lemma_put2 em f x y f' x' in
    FStar.Classical.forall_intro_2 aux

let lemma_bodies_extend (defs:list D.definition) (g:CG.cgraph) (bodies:I.index_tree nat) (i b:nat)
  : Lemma (requires bodies_ok defs g bodies /\ i < L.length defs /\ b < CG.node_count g /\
                    CG.value_of g b == Some (L.index defs i).D.body)
          (ensures bodies_ok defs g (I.index_put bodies i b))
  = let aux (j:nat) : Lemma (match I.index_get (I.index_put bodies i b) j with
                             | Some b' -> j < L.length defs /\ b' < CG.node_count g /\ CG.value_of g b' == Some (L.index defs j).D.body
                             | None -> True)
      = I.lemma_index_put bodies i b j in
    FStar.Classical.forall_intro aux

let rec lemma_exp_args (defs:list D.definition) (f:nat) (g:CG.cgraph) (em:memo2) (xs:list nat) (args:list expr)
  : Lemma (requires em_ok defs g em /\ CG.values_of g xs == Some args)
          (ensures (match I.opt_map (get2 em f) xs with
                    | Some ys -> CS.all_below ys (CG.node_count g) /\
                                (match CG.values_of g ys with
                                 | Some vs -> D.expand_args f defs args == Some vs
                                 | None -> False)
                    | None -> True))
          (decreases xs)
  = match xs, args with
    | x :: xs', _ :: args' ->
      lemma_exp_args defs f g em xs' args';
      (match get2 em f x with Some y -> assert (exp_in defs f g x y) | None -> ())
    | _, _ -> ()

let rec eenters (f:nat) (xs:list nat) (tail:list eframe) : Tot (list eframe) (decreases xs) =
  match xs with
  | [] -> tail
  | x :: rest -> eenters f rest (EEnter f x :: tail)

let lemma_stack_cons (defs:list D.definition) (g:CG.cgraph) (fr:eframe) (rest:list eframe)
  : Lemma (requires frame_ok defs g fr /\ stack_ok defs g rest) (ensures stack_ok defs g (fr :: rest))
  = ()

let rec lemma_eenters (defs:list D.definition) (g:CG.cgraph) (f:nat) (xs:list nat) (tail:list eframe)
  : Lemma (requires stack_ok defs g tail) (ensures stack_ok defs g (eenters f xs tail)) (decreases xs)
  = match xs with [] -> () | x :: rest -> lemma_eenters defs g f rest (EEnter f x :: tail)

noeq
type estep =
  | ENext : graph:CG.cgraph -> em:memo2 -> bodies:I.index_tree nat -> stack:list eframe -> estep
  | EHalt : built:CG.built -> estep

let estep_ok (defs:list D.definition) (g:CG.cgraph) (r:estep) : prop =
  match r with
  | ENext g' em' bodies' st' -> einv defs g' em' bodies' st' /\ CG.cgrows g g'
  | EHalt b -> ~(CG.Built? b)

(* The expansion `y` of `x` with fuel `f`, recorded in the memo (its update charged). *)
let eput (defs:list D.definition) (f:nat) (g0 g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (x y:nat) (rest:list eframe)
  : Pure estep (requires einv defs g em bodies rest /\ CG.cgrows g0 g /\ exp_in defs f g x y)
               (ensures fun r -> estep_ok defs g0 r) =
  match charge g 0 memo_units with
  | Some g1 ->
    lemma_charge g 0 memo_units;
    lemma_einv_grows defs g g1 em bodies rest;
    lemma_em_extend defs g1 em f x y;
    CG.lemma_cgrows_trans g0 g g1;
    ENext g1 (put2 em f x y) bodies rest
  | None -> EHalt (CG.BuildExhausted T.Storage)

(* --- One step of `D.expand`, by kind --------------------------------------------------------------- *)

let lemma_expand_var (defs:list D.definition) (f:nat) (e:expr)
  : Lemma (requires Var? e \/ Nil? defs) (ensures D.expand f defs e == Some e)
  = ()

let lemma_expand_quant (defs:list D.definition) (f:nat) (k:quantifier_kind) (bs:list sort) (q:sort) (b b':expr)
  : Lemma (requires Cons? defs /\ D.expand f defs b == Some b')
          (ensures D.expand f defs (Quantifier k bs q b) == Some (Quantifier k bs q b'))
  = ()

let lemma_expand_plain_app (defs:list D.definition) (f:nat) (fd:func_decl) (args vs:list expr)
  : Lemma (requires Cons? defs /\ D.expand_args f defs args == Some vs /\ D.lookup defs fd == None)
          (ensures D.expand f defs (App fd args) == Some (App fd vs))
  = ()

let lemma_expand_def_app (defs:list D.definition) (f:nat) (fd:func_decl) (args vs:list expr) (d:D.definition) (vz:expr)
  : Lemma (requires Cons? defs /\ f > 0 /\ D.expand_args f defs args == Some vs /\ D.lookup defs fd == Some d /\
                    D.instantiate 0 d.D.variables vs d.D.body == Some vz)
          (ensures D.expand f defs (App fd args) == D.expand (f - 1) defs vz)
  = ()

let exp_enter (defs:list D.definition) (f:nat) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (x:nat) (rest:list eframe)
  : Pure estep (requires einv defs g em bodies rest) (ensures fun r -> estep_ok defs g r) =
  CG.lemma_cgrows_refl g;
  if x >= CG.node_count g then EHalt CG.BuildInvalid
  else match get2 em f x with
  | Some _ -> ENext g em bodies rest
  | None ->
    match CG.node_of g x, CG.value_of g x with
    | _, Some (Var _ _) ->
      let Some v = CG.value_of g x in
      lemma_expand_var defs f v;
      eput defs f g g em bodies x x rest
    | Some (T.ENApp _ xs _), Some (App _ _) ->
      if Nil? defs then (let Some v = CG.value_of g x in lemma_expand_var defs f v; eput defs f g g em bodies x x rest)
      else (match push g (1 + L.length xs) with
            | Some g1 ->
              lemma_einv_grows defs g g1 em bodies rest;
              lemma_stack_cons defs g1 (EExit f x) rest;
              lemma_eenters defs g1 f xs (EExit f x :: rest);
              ENext g1 em bodies (eenters f xs (EExit f x :: rest))
            | None -> EHalt (CG.BuildExhausted T.Storage))
    | Some (T.ENQuant _ _ y _), Some (Quantifier _ _ _ _) ->
      if Nil? defs then (let Some v = CG.value_of g x in lemma_expand_var defs f v; eput defs f g g em bodies x x rest)
      else (match push g 2 with
            | Some g1 ->
              lemma_einv_grows defs g g1 em bodies rest;
              lemma_stack_cons defs g1 (EExit f x) rest;
              lemma_stack_cons defs g1 (EEnter f y) (EExit f x :: rest);
              ENext g1 em bodies (EEnter f y :: EExit f x :: rest)
            | None -> EHalt (CG.BuildExhausted T.Storage))
    | _, _ -> EHalt CG.BuildInvalid

let exp_exit_quant (defs:list D.definition) (f:nat) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (x y:nat) (rest:list eframe)
  : Pure estep (requires einv defs g em bodies rest /\ x < CG.node_count g /\ Cons? defs /\
                         (match CG.node_of g x, CG.value_of g x with
                          | Some (T.ENQuant _ _ y' _), Some (Quantifier _ _ _ _) -> y' == y
                          | _, _ -> False))
               (ensures fun r -> estep_ok defs g r) =
  CG.lemma_cgrows_refl g;
  assert (CG.node_exact g x);
  CG.reveal_exact g x;
  match get2 em f y with
  | None -> EHalt CG.BuildInvalid
  | Some z ->
    assert (exp_in defs f g y z);
    let Some (Quantifier k bs q b) = CG.value_of g x in
    let Some b' = CG.value_of g z in
    lemma_expand_quant defs f k bs q b b';
    if z = y then eput defs f g g em bodies x x rest
    else begin
      lemma_rebuild_quant g x z;
      match rebuild_quant g x z with
      | CG.Built g2 w ->
        lemma_einv_grows defs g g2 em bodies rest;
        assert (exp_in defs f g2 x w);
        eput defs f g g2 em bodies x w rest
      | CG.BuildExhausted p -> EHalt (CG.BuildExhausted p)
      | CG.BuildInvalid -> EHalt CG.BuildInvalid
    end

(* The application `x` without a definition, from its expanded arguments `ys`. *)
let exp_plain_app (defs:list D.definition) (f:nat) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat)
                  (x:nat) (xs ys:list nat) (vs:list expr) (rest:list eframe)
  : Pure estep (requires einv defs g em bodies rest /\ x < CG.node_count g /\ Cons? defs /\
                         CG.values_of g ys == Some vs /\
                         (match CG.node_of g x, CG.value_of g x with
                          | Some (T.ENApp _ xs' _), Some (App fd args) ->
                            xs' == xs /\ CG.values_of g xs == Some args /\
                            D.expand_args f defs args == Some vs /\ D.lookup defs fd == None
                          | _, _ -> False))
               (ensures fun r -> estep_ok defs g r) =
  CG.lemma_cgrows_refl g;
  CS.lemma_same_ids ys xs;
  let Some (App fd args) = CG.value_of g x in
  lemma_expand_plain_app defs f fd args vs;
  if CS.same_ids ys xs then eput defs f g g em bodies x x rest
  else begin
    lemma_rebuild_app g x ys;
    match rebuild_app g x ys with
    | CG.Built g2 y ->
      lemma_einv_grows defs g g2 em bodies rest;
      assert (exp_in defs f g2 x y);
      eput defs f g g2 em bodies x y rest
    | CG.BuildExhausted p -> EHalt (CG.BuildExhausted p)
    | CG.BuildInvalid -> EHalt CG.BuildInvalid
  end

let exp_then (defs:list D.definition) (f x z:nat) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (rest:list eframe)
  : Pure estep (requires einv defs g em bodies rest /\ frame_ok defs g (EThen f x z)) (ensures fun r -> estep_ok defs g r) =
  CG.lemma_cgrows_refl g;
  match get2 em (f - 1) z with
  | Some w -> assert (exp_in defs (f - 1) g z w); eput defs f g g em bodies x w rest
  | None -> EHalt CG.BuildInvalid

noeq
type body_result =
  | BodyNode : graph:CG.cgraph -> bodies:I.index_tree nat -> node:nat -> body_result
  | BodyStopped : built:CG.built -> body_result

(* The node of the body of the definition at position `i`: interned once
   per expansion, then found by its position. *)
let body_node (defs:list D.definition) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (i:nat) (rest:list eframe)
  : Pure body_result (requires einv defs g em bodies rest /\ i < L.length defs)
                     (ensures fun r -> match r with
                                    | BodyNode g' bodies' b -> einv defs g' em bodies' rest /\ CG.cgrows g g' /\
                                                              b < CG.node_count g' /\ CG.value_of g' b == Some (L.index defs i).D.body
                                    | BodyStopped b -> ~(CG.Built? b)) =
  match charge g CS.table_units 0 with
  | None -> BodyStopped (CG.BuildExhausted T.Preparation)
  | Some g0 ->
    lemma_charge g CS.table_units 0;
    lemma_einv_grows defs g g0 em bodies rest;
    match I.index_get bodies i with
    | Some b -> BodyNode g0 bodies b
    | None ->
      match intern_expr g0 (L.index defs i).D.body with
      | InternStopped b -> BodyStopped b
      | Interned g1 b ->
        match charge g1 0 (1 + CS.table_units) with
        | None -> BodyStopped (CG.BuildExhausted T.Storage)
        | Some g2 ->
          lemma_charge g1 0 (1 + CS.table_units);
          CG.lemma_cgrows_trans g0 g1 g2;
          CG.lemma_cgrows_trans g g0 g2;
          lemma_einv_grows defs g0 g2 em bodies rest;
          lemma_bodies_extend defs g2 bodies i b;
          BodyNode g2 (I.index_put bodies i b) b

(* The application `x` of the definition `d` (at position `i`), from its
   expanded arguments `ys`: the instance of `d`'s body, then its expansion
   with one less fuel (`EThen`). *)
let lemma_then_equation (defs:list D.definition) (f:nat) (g g3:CG.cgraph) (x z b:nat) (ys:list nat) (vs:list expr)
                        (d:D.definition)
  : Lemma (requires CG.cgrows g g3 /\ x < CG.node_count g /\ f > 0 /\ Cons? defs /\
                    inst_in d.D.variables ys 0 g3 b z /\ CG.values_of g3 ys == Some vs /\
                    CG.value_of g3 b == Some d.D.body /\
                    (match CG.value_of g x with
                     | Some (App fd args) -> D.expand_args f defs args == Some vs /\ D.lookup defs fd == Some d
                     | _ -> False))
          (ensures frame_ok defs g3 (EThen f x z))
  = let Some (App fd args) = CG.value_of g x in
    let Some vz = CG.value_of g3 z in
    lemma_expand_def_app defs f fd args vs d vz

let exp_def_app (defs:list D.definition) (f:nat) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat)
                (x:nat) (ys:list nat) (vs:list expr) (i:nat) (d:D.definition) (rest:list eframe)
  : Pure estep (requires einv defs g em bodies rest /\ x < CG.node_count g /\ f > 0 /\
                         CS.all_below ys (CG.node_count g) /\ CG.values_of g ys == Some vs /\
                         i < L.length defs /\ L.index defs i == d /\
                         (match CG.value_of g x with
                          | Some (App fd args) -> D.expand_args f defs args == Some vs /\ D.lookup defs fd == Some d
                          | _ -> False))
               (ensures fun r -> estep_ok defs g r) =
  match body_node defs g em bodies i rest with
  | BodyStopped b -> EHalt b
  | BodyNode g1 bodies1 b ->
    T.lemma_all_below_widen ys (CG.node_count g) (CG.node_count g1);
    CG.lemma_values_of_grows g g1 ys;
    (match ginst d.D.variables ys g1 b with
     | InstStopped bb -> EHalt bb
     | InstNode g2 z ->
       lemma_einv_grows defs g1 g2 em bodies1 rest;
       CG.lemma_values_of_grows g1 g2 ys;
       CG.lemma_cgrows_trans g g1 g2;
       (match push g2 2 with
        | None -> EHalt (CG.BuildExhausted T.Storage)
        | Some g3 ->
          lemma_einv_grows defs g2 g3 em bodies1 rest;
          CG.lemma_cgrows_trans g g2 g3;
          CG.lemma_cgrows_trans g1 g2 g3;
          T.lemma_all_below_widen ys (CG.node_count g1) (CG.node_count g2);
          lemma_inst_in_grows d.D.variables ys 0 g2 g3 b z;
          CG.lemma_values_of_grows g2 g3 ys;
          assert (CG.value_of g3 b == CG.value_of g1 b);
          lemma_then_equation defs f g g3 x z b ys vs d;
          lemma_stack_cons defs g3 (EThen f x z) rest;
          lemma_stack_cons defs g3 (EEnter (f - 1) z) (EThen f x z :: rest);
          ENext g3 em bodies1 (EEnter (f - 1) z :: EThen f x z :: rest)))

let exp_exit_app (defs:list D.definition) (f:nat) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat)
                 (x:nat) (xs:list nat) (rest:list eframe)
  : Pure estep (requires einv defs g em bodies rest /\ x < CG.node_count g /\ Cons? defs /\
                         (match CG.node_of g x, CG.value_of g x with
                          | Some (T.ENApp _ xs' _), Some (App _ _) -> xs' == xs
                          | _, _ -> False))
               (ensures fun r -> estep_ok defs g r) =
  FStar.Math.Lemmas.nat_times_nat_is_nat (L.length xs) CS.table_units;
  let cp : nat = L.length xs * CS.table_units + 1 + L.length defs in
  match charge g cp 0 with
  | None -> EHalt (CG.BuildExhausted T.Preparation)
  | Some g1 ->
    lemma_charge g cp 0;
    lemma_einv_grows defs g g1 em bodies rest;
    assert (CG.node_exact g1 x);
    CG.reveal_exact g1 x;
    opt_map_tail_is (get2 em f) xs;
    let Some (App fd args) = CG.value_of g1 x in
    lemma_exp_args defs f g1 em xs args;
    match I.opt_map_tail (get2 em f) xs with
    | None -> EHalt CG.BuildInvalid
    | Some ys ->
      lemma_values_some g1 ys;
      let Some vs = CG.values_of g1 ys in
      lemma_find_def defs fd 0;
      let r =
        match find_def defs fd 0 with
        | None -> exp_plain_app defs f g1 em bodies x xs ys vs rest
        | Some (i, d) ->
          if f = 0 then EHalt CG.BuildInvalid
          else exp_def_app defs f g1 em bodies x ys vs i d rest in
      (match r with ENext g2 _ _ _ -> CG.lemma_cgrows_trans g g1 g2 | _ -> ());
      r

let exp_exit (defs:list D.definition) (f:nat) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (x:nat) (rest:list eframe)
  : Pure estep (requires einv defs g em bodies rest) (ensures fun r -> estep_ok defs g r) =
  CG.lemma_cgrows_refl g;
  if x >= CG.node_count g then EHalt CG.BuildInvalid
  else match get2 em f x with
  | Some _ -> ENext g em bodies rest
  | None ->
    if Nil? defs then begin
      assert (CG.node_exact g x);
      CG.reveal_exact g x;
      let Some v = CG.value_of g x in
      lemma_expand_var defs f v;
      eput defs f g g em bodies x x rest
    end
    else match CG.node_of g x, CG.value_of g x with
    | Some (T.ENApp _ xs _), Some (App _ _) -> exp_exit_app defs f g em bodies x xs rest
    | Some (T.ENQuant _ _ y _), Some (Quantifier _ _ _ _) -> exp_exit_quant defs f g em bodies x y rest
    | _, _ -> EHalt CG.BuildInvalid

let exp_frame (defs:list D.definition) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (fr:eframe) (rest:list eframe)
  : Pure estep (requires einv defs g em bodies (fr :: rest)) (ensures fun r -> estep_ok defs g r) =
  match charge g memo_units 0 with
  | None -> EHalt (CG.BuildExhausted T.Preparation)
  | Some g0 ->
    lemma_charge g memo_units 0;
    lemma_einv_grows defs g g0 em bodies (fr :: rest);
    let s = match fr with
      | EEnter f x -> exp_enter defs f g0 em bodies x rest
      | EExit f x -> exp_exit defs f g0 em bodies x rest
      | EThen f x z -> exp_then defs f x z g0 em bodies rest in
    (match s with ENext g1 _ _ _ -> CG.lemma_cgrows_trans g g0 g1 | _ -> ());
    s

[@@"opaque_to_smt"]
let einv_o (defs:list D.definition) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (st:list eframe) : prop =
  einv defs g em bodies st

let reveal_einv (defs:list D.definition) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (st:list eframe)
  : Lemma (einv_o defs g em bodies st <==> einv defs g em bodies st)
  = FStar.Pervasives.reveal_opaque (`%einv_o) (einv_o defs g em bodies st)

let estep_ok_o (defs:list D.definition) (g:CG.cgraph) (r:estep) : prop =
  match r with
  | ENext g' em' bodies' st' -> einv_o defs g' em' bodies' st' /\ CG.cgrows g g'
  | EHalt b -> ~(CG.Built? b)

let exp_frame_o (defs:list D.definition) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (fr:eframe) (rest:list eframe)
  : Pure estep (requires einv_o defs g em bodies (fr :: rest)) (ensures fun r -> estep_ok_o defs g r) =
  reveal_einv defs g em bodies (fr :: rest);
  let r = exp_frame defs g em bodies fr rest in
  (match r with ENext g' em' bodies' st' -> reveal_einv defs g' em' bodies' st' | _ -> ());
  r

noeq
type erun =
  | ERan : graph:CG.cgraph -> em:memo2 -> bodies:I.index_tree nat -> erun
  | EStopped : built:CG.built -> erun

let erun_ok (defs:list D.definition) (g:CG.cgraph) (r:erun) : prop =
  match r with
  | ERan g' em' bodies' -> einv_o defs g' em' bodies' [] /\ CG.cgrows g g'
  | EStopped b -> ~(CG.Built? b)

let lemma_erun_trans (defs:list D.definition) (g g1:CG.cgraph) (r:erun)
  : Lemma (requires CG.cgrows g g1 /\ erun_ok defs g1 r) (ensures erun_ok defs g r)
  = match r with ERan g2 _ _ -> CG.lemma_cgrows_trans g g1 g2 | _ -> ()

let rec exp_loop (defs:list D.definition) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (stack:list eframe) (steps:nat)
  : Pure erun (requires einv_o defs g em bodies stack) (ensures fun r -> erun_ok defs g r) (decreases steps) =
  match stack with
  | [] -> CG.lemma_cgrows_refl g; ERan g em bodies
  | fr :: rest ->
    if steps = 0 then EStopped (CG.BuildExhausted T.Preparation)
    else match exp_frame_o defs g em bodies fr rest with
      | ENext g1 em1 bodies1 stack1 ->
        let r = exp_loop defs g1 em1 bodies1 stack1 (steps - 1) in
        lemma_erun_trans defs g g1 r;
        r
      | EHalt b -> EStopped b

(* The expansions with fuel `f` of the roots `xs`, one after the other,
   sharing one memo. *)
let rec exp_roots (defs:list D.definition) (f:nat) (g:CG.cgraph) (em:memo2) (bodies:I.index_tree nat) (xs:list nat)
  : Pure erun (requires einv_o defs g em bodies []) (ensures fun r -> erun_ok defs g r) (decreases xs) =
  match xs with
  | [] -> CG.lemma_cgrows_refl g; ERan g em bodies
  | x :: rest ->
    reveal_einv defs g em bodies [];
    reveal_einv defs g em bodies [EEnter f x];
    match exp_loop defs g em bodies [EEnter f x] g.CG.prep with
    | ERan g1 em1 bodies1 ->
      let r = exp_roots defs f g1 em1 bodies1 rest in
      lemma_erun_trans defs g g1 r;
      r
    | EStopped b -> EStopped b

let rec lemma_expanded_list (defs:list D.definition) (f:nat) (g:CG.cgraph) (em:memo2) (xs:list nat) (vs:list expr)
  : Lemma (requires em_ok defs g em /\ CG.values_of g xs == Some vs)
          (ensures (match I.opt_map (get2 em f) xs with
                    | Some ys -> CS.all_below ys (CG.node_count g) /\
                                (match CG.values_of g ys with
                                 | Some ws -> I.opt_map (D.expand f defs) vs == Some ws
                                 | None -> False)
                    | None -> True))
          (decreases xs)
  = match xs, vs with
    | x :: xs', _ :: vs' ->
      lemma_expanded_list defs f g em xs' vs';
      (match get2 em f x with Some y -> assert (exp_in defs f g x y) | None -> ())
    | _, _ -> ()

noeq
type expanded =
  | ExpandedNodes : graph:CG.cgraph -> bodies:I.index_tree nat -> nodes:list nat -> expanded
  | ExpandStopped : built:CG.built -> expanded

(* The nodes storing `D.expand f defs` of the expressions of `xs`, in order;
   `bodies`, the nodes of the definitions' bodies imported before (by a
   document's earlier expansions with the same `defs`), is reused and
   extended. *)
let expand_nodes (defs:list D.definition) (f:nat) (g:CG.cgraph) (bodies0:I.index_tree nat) (xs:list nat)
  : Pure expanded (requires CG.graph_inv g /\ CS.all_below xs (CG.node_count g) /\ bodies_ok defs g bodies0)
                  (ensures fun r -> match r with
                                 | ExpandedNodes g' bodies' ys ->
                                   CG.graph_inv g' /\ CG.cgrows g g' /\ CS.all_below ys (CG.node_count g') /\
                                   bodies_ok defs g' bodies' /\
                                   (match CG.values_of g xs, CG.values_of g' ys with
                                    | Some vs, Some ws -> I.opt_map (D.expand f defs) vs == Some ws
                                    | _, _ -> False)
                                 | ExpandStopped b -> ~(CG.Built? b)) =
  assert (em_ok defs g I.Empty);
  reveal_einv defs g I.Empty bodies0 [];
  match exp_roots defs f g I.Empty bodies0 xs with
  | EStopped b -> ExpandStopped b
  | ERan g1 em bodies ->
    reveal_einv defs g1 em bodies [];
    FStar.Math.Lemmas.nat_times_nat_is_nat (L.length xs) CS.table_units;
    let cp : nat = L.length xs * CS.table_units in
    match charge g1 cp 0 with
    | None -> ExpandStopped (CG.BuildExhausted T.Preparation)
    | Some g2 ->
      lemma_charge g1 cp 0;
      CG.lemma_cgrows_trans g g1 g2;
      lemma_values_some g xs;
      CG.lemma_values_of_grows g g2 xs;
      opt_map_tail_is (get2 em f) xs;
      let Some vs = CG.values_of g2 xs in
      lemma_em_grows defs g1 g2 em;
      lemma_expanded_list defs f g2 em xs vs;
      lemma_bodies_grows defs g1 g2 bodies;
      match I.opt_map_tail (get2 em f) xs with
      | Some ys -> ExpandedNodes g2 bodies ys
      | None -> ExpandStopped CG.BuildInvalid
