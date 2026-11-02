(*
   Z3CheckedExpansion.fst

   Definition expansion on the checked graph of the opt-in mode
   `verified-dag-v1` (in progress). The constructors below build, from nodes
   of an invariant graph, the node of `Z3Definitions.lift` one level at a
   time: from the node `x` and the nodes of its lifted children, the lifted
   node, which stores exactly `D.lift a c (value_of g x)`. They read nodes and
   stored expressions by id and never compare expressions; a node whose sort
   conditions do not hold (`ok` false) is not lifted (`BuildInvalid`).
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

(* `y` in `g'` stores the lift of what `x` stores in `g`. *)
let lifted (a c:nat) (g g':CG.cgraph) (x y:nat) : prop =
  CG.graph_inv g' /\ CG.cgrows g g' /\ y < CG.node_count g' /\
  (match CG.value_of g x with Some v -> CG.value_of g' y == Some (D.lift a c v) | None -> False)

(* --- Sorts are kept by lifting ---------------------------------------------------------------- *)

let lemma_lift_sort (a c:nat) (e:expr) : Lemma (get_sort (D.lift a c e) == get_sort e) =
  match e with Var _ _ -> () | App _ _ -> () | Quantifier _ _ _ _ -> ()

let rec lemma_lift_args_sorts (a c:nat) (args:list expr)
  : Lemma (ensures L.map get_sort (D.lift_args a c args) == L.map get_sort args) (decreases args)
  = match args with
    | [] -> ()
    | e :: rest -> lemma_lift_sort a c e; lemma_lift_args_sorts a c rest

(* --- A variable ---------------------------------------------------------------------------------- *)

let lift_var (a c:nat) (g:CG.cgraph) (x:nat) : CG.built =
  match CG.node_of g x, CG.value_of g x with
  | Some (T.ENVar _ i), Some (Var n s) -> CG.add_var g (lift_index a c n) (s, i)
  | _, _ -> CG.BuildInvalid

let lemma_lift_var (a c:nat) (g:CG.cgraph) (x:nat)
  : Lemma (requires CG.graph_inv g /\ x < CG.node_count g)
          (ensures (match lift_var a c g x with CG.Built g' y -> lifted a c g g' x y | _ -> True))
  = assert (CG.node_exact g x);
    CG.reveal_exact g x;
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENVar _ i), Some (Var n s) -> CG.lemma_add_var g (lift_index a c n) (s, i)
    | _, _ -> ()

(* --- An application, from its lifted arguments ------------------------------------------------- *)

(* The application of `x`'s declaration to the nodes `ys`, its domain the
   sort ids of `ys` (read and charged), its range `x`'s. *)
let lift_app (g:CG.cgraph) (x:nat) (ys:list nat) : CG.built =
  match CG.node_of g x, CG.value_of g x with
  | Some (T.ENApp ok _ i), Some (App f _) ->
    if not ok then CG.BuildInvalid
    else (match CG.read_children g ys [] [] g.CG.prep g.CG.store with
          | CG.ChildrenRead _ ss p s ->
            CG.add_app ({ g with CG.prep = p; CG.store = s }) ({ CG.decl = f; CG.dom = ss; CG.rng = i }) ys
          | CG.ChildrenExhausted ph -> CG.BuildExhausted ph
          | CG.ChildrenInvalid -> CG.BuildInvalid)
  | _, _ -> CG.BuildInvalid

let lemma_lift_app (a c:nat) (g:CG.cgraph) (x:nat) (ys:list nat)
  : Lemma (requires CG.graph_inv g /\ x < CG.node_count g /\
                    (match CG.value_of g x with
                     | Some (App _ args) -> CG.values_of g ys == Some (D.lift_args a c args)
                     | _ -> True))
          (ensures (match lift_app g x ys with CG.Built g' y -> lifted a c g g' x y | _ -> True))
  = assert (CG.node_exact g x);
    CG.reveal_exact g x;
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENApp ok _ i), Some (App f args) ->
      if not ok then ()
      else begin
        CG.lemma_read_children_ok g ys g.CG.prep g.CG.store;
        match CG.read_children g ys [] [] g.CG.prep g.CG.store with
        | CG.ChildrenRead vs ss p s ->
          let g1 = { g with CG.prep = p; CG.store = s } in
          CG.lemma_budget g p s;
          T.lemma_sorts_match_map args f.domain;
          lemma_lift_args_sorts a c args;
          let d = { CG.decl = f; CG.dom = ss; CG.rng = i } in
          assert (CG.decl_ok g1 d);
          CG.lemma_add_app g1 d ys;
          CG.lemma_values_of_grows g g1 ys;
          (match CG.add_app g1 d ys with
           | CG.Built g' _ -> CG.lemma_cgrows_trans g g1 g'
           | _ -> ())
        | _ -> ()
      end
    | _, _ -> ()

(* --- A quantifier, from its lifted body ----------------------------------------------------------- *)

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

(* The quantifier of `x` (its kind and bound sorts, by their ids) over the body node `z`. *)
let lift_quant (g:CG.cgraph) (x z:nat) : CG.built =
  match CG.node_of g x, CG.value_of g x with
  | Some (T.ENQuant ok ys _ _), Some (Quantifier k bs _ _) ->
    if not ok then CG.BuildInvalid else CG.add_quant g k (pair_sorts bs ys) z
  | _, _ -> CG.BuildInvalid

let lemma_lift_quant (a c:nat) (g:CG.cgraph) (x z:nat)
  : Lemma (requires CG.graph_inv g /\ x < CG.node_count g /\
                    (match CG.value_of g x with
                     | Some (Quantifier _ bs _ b) -> CG.value_of g z == Some (D.lift a (c + L.length bs) b)
                     | _ -> True))
          (ensures (match lift_quant g x z with CG.Built g' y -> lifted a c g g' x y | _ -> True))
  = assert (CG.node_exact g x);
    CG.reveal_exact g x;
    match CG.node_of g x, CG.value_of g x with
    | Some (T.ENQuant ok ys _ _), Some (Quantifier k bs q b) ->
      if not ok then ()
      else begin
        lemma_pair_sorts g bs ys;
        lemma_lift_sort a (c + L.length bs) b;
        CG.lemma_add_quant g k (pair_sorts bs ys) z
      end
    | _, _ -> ()

(* --- The lift of a node, memoised by context ---------------------------------------------------- *)

(* The memo of a lifting run: for each context key (shift `a`, cutoff `c`,
   node `x`) the node storing the lift of `x`. A memo is only meaningful with
   the graph it was built on and the graphs grown from it (`memo_ok`); it is
   never taken from another run. *)
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

(* The memo's lookups and updates, charged to the graph's own budgets. *)
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

noeq
type lifting =
  | LiftedNode : graph:CG.cgraph -> memo:lift_memo -> node:nat -> lifting
  | LiftedNodes : graph:CG.cgraph -> memo:lift_memo -> nodes:list nat -> lifting
  | LiftStopped : built:CG.built -> lifting

let lift_node_ok (a c:nat) (g:CG.cgraph) (x:nat) (r:lifting) : prop =
  match r with
  | LiftedNode g' m' y -> CG.graph_inv g' /\ CG.cgrows g g' /\ memo_ok g' m' /\ lifted_in a c g' x y
  | LiftedNodes _ _ _ -> False
  | LiftStopped b -> ~(CG.Built? b)

let lift_nodes_ok (a c:nat) (g:CG.cgraph) (xs:list nat) (r:lifting) : prop =
  match r with
  | LiftedNodes g' m' ys ->
    CG.graph_inv g' /\ CG.cgrows g g' /\ memo_ok g' m' /\ CS.all_below ys (CG.node_count g') /\
    (match CG.values_of g xs with Some vs -> CG.values_of g' ys == Some (D.lift_args a c vs) | None -> False)
  | LiftedNode _ _ _ -> False
  | LiftStopped b -> ~(CG.Built? b)

let lemma_lifted_in (a c:nat) (g0 g g' g'':CG.cgraph) (x y:nat)
  : Lemma (requires CG.cgrows g0 g /\ x < CG.node_count g0 /\ lifted a c g g' x y /\
                    CG.cgrows g' g'' /\ CG.node_count g'' == CG.node_count g')
          (ensures CG.cgrows g0 g'' /\ lifted_in a c g'' x y)
  = CG.lemma_cgrows_trans g0 g g';
    CG.lemma_cgrows_trans g0 g' g'';
    assert (CG.value_of g x == CG.value_of g0 x);
    assert (CG.value_of g'' x == CG.value_of g0 x);
    assert (CG.value_of g'' y == CG.value_of g' y)

(* A lift built from `g` (grown from `g0`): recorded in the memo under its
   context key, the memo's update charged. *)
let finish (a c:nat) (g0:CG.cgraph) (g:CG.cgraph{CG.graph_inv g /\ CG.cgrows g0 g}) (m:lift_memo{memo_ok g m})
           (x:nat{x < CG.node_count g0}) (b:CG.built)
  : Pure lifting (requires (match b with CG.Built g' y -> lifted a c g g' x y | _ -> True))
                 (ensures fun r -> lift_node_ok a c g0 x r) =
  match b with
  | CG.Built g' y ->
    lemma_memo_grows g g' m;
    (match charge g' 0 memo_units with
     | Some g'' ->
       lemma_charge g' 0 memo_units;
       lemma_memo_grows g' g'' m;
       lemma_lifted_in a c g0 g g' g'' x y;
       lemma_memo_extend g'' m a c x y;
       let r = LiftedNode g'' (memo_put m a c x y) y in
       assert (lift_node_ok a c g0 x r);
       r
     | None -> LiftStopped (CG.BuildExhausted T.Storage))
  | CG.BuildExhausted p -> LiftStopped (CG.BuildExhausted p)
  | CG.BuildInvalid -> LiftStopped CG.BuildInvalid

(* A result for `x` from `g0` is one for `x` from `g`, when `g0` grew from `g`. *)
let lemma_node_ok_back (a c:nat) (g g0:CG.cgraph) (x:nat) (r:lifting)
  : Lemma (requires CG.cgrows g g0 /\ lift_node_ok a c g0 x r) (ensures lift_node_ok a c g x r)
  = match r with
    | LiftedNode g' _ _ -> CG.lemma_cgrows_trans g g0 g'
    | _ -> ()

(* The application step: from the lifts of the arguments. *)
let lift_app_step (a c:nat) (g:CG.cgraph{CG.graph_inv g}) (x:nat{x < CG.node_count g}) (xs:list nat)
                  (r:lifting{lift_nodes_ok a c g xs r})
  : Pure lifting (requires (match CG.node_of g x, CG.value_of g x with
                            | Some (T.ENApp _ xs' _), Some (App _ _) -> xs' == xs
                            | _, _ -> False))
                 (ensures fun r' -> lift_node_ok a c g x r') =
  match r with
  | LiftedNodes g1 m1 ys ->
    assert (CG.node_exact g x);
    CG.reveal_exact g x;
    lemma_lift_app a c g1 x ys;
    finish a c g g1 m1 x (lift_app g1 x ys)
  | LiftStopped b -> LiftStopped b

(* The quantifier step: from the lift of the body under the raised cutoff. *)
let lift_quant_step (a c:nat) (g:CG.cgraph{CG.graph_inv g}) (x:nat{x < CG.node_count g}) (y:nat) (n:nat)
                    (r:lifting{lift_node_ok a (c + n) g y r})
  : Pure lifting (requires (match CG.node_of g x, CG.value_of g x with
                            | Some (T.ENQuant _ _ y' _), Some (Quantifier _ bs _ _) -> y' == y /\ n == L.length bs
                            | _, _ -> False))
                 (ensures fun r' -> lift_node_ok a c g x r') =
  match r with
  | LiftedNode g1 m1 z ->
    assert (CG.node_exact g x);
    CG.reveal_exact g x;
    assert (CG.value_of g1 y == CG.value_of g y);
    lemma_lift_quant a c g1 x z;
    finish a c g g1 m1 x (lift_quant g1 x z)
  | LiftStopped b -> LiftStopped b

(* The lift of node `x` with shift `a` under cutoff `c`: a memo hit, or the
   node built from the lifts of its children (a quantifier's body under the
   cutoff raised by its binders). Children must be earlier nodes. The lift
   itself (`D.lift`) appears only in the specification: the nodes are built
   from the lifted children. *)
let rec glift (a c:nat) (g:CG.cgraph{CG.graph_inv g}) (m:lift_memo{memo_ok g m}) (x:nat{x < CG.node_count g})
  : Tot (r:lifting{lift_node_ok a c g x r}) (decreases %[x; 1]) =
  match charge g memo_units 0 with
  | None -> LiftStopped (CG.BuildExhausted T.Preparation)
  | Some g0 ->
    lemma_charge g memo_units 0;
    lemma_memo_grows g g0 m;
    match memo_get m a c x with
    | Some y -> LiftedNode g0 m y
    | None ->
      assert (CG.node_exact g0 x);
      CG.reveal_exact g0 x;
      let r : r:lifting{lift_node_ok a c g0 x r} =
        match CG.node_of g0 x, CG.value_of g0 x with
        | Some (T.ENVar _ _), Some (Var _ _) ->
          lemma_lift_var a c g0 x;
          CG.lemma_cgrows_refl g0;
          finish a c g0 g0 m x (lift_var a c g0 x)
        | Some (T.ENApp _ xs _), Some (App _ _) ->
          T.lemma_all_below_widen xs x (CG.node_count g0);
          lift_app_step a c g0 x xs (glift_list x a c g0 m xs)
        | Some (T.ENQuant _ _ y _), Some (Quantifier _ bs _ _) ->
          lift_quant_step a c g0 x y (L.length bs) (glift a (c + L.length bs) g0 m y)
        | _, _ -> LiftStopped CG.BuildInvalid in
      lemma_node_ok_back a c g g0 x r;
      r

(* The lifts of the nodes `xs`, all earlier than `bound`, in order. *)
and glift_list (bound a c:nat) (g:CG.cgraph{CG.graph_inv g}) (m:lift_memo{memo_ok g m})
               (xs:list nat{CS.all_below xs bound /\ CS.all_below xs (CG.node_count g)})
  : Tot (r:lifting{lift_nodes_ok a c g xs r}) (decreases %[bound; 0; xs]) =
  match xs with
  | [] -> LiftedNodes g m []
  | x :: rest ->
    match glift a c g m x with
    | LiftedNode g1 m1 y ->
      T.lemma_all_below_widen rest (CG.node_count g) (CG.node_count g1);
      (match glift_list bound a c g1 m1 rest with
       | LiftedNodes g2 m2 ys ->
         CG.lemma_values_of_grows g g1 rest;
         CG.lemma_cgrows_trans g g1 g2;
         assert (CG.value_of g2 y == CG.value_of g1 y);
         assert (CG.value_of g1 x == CG.value_of g x);
         LiftedNodes g2 m2 (y :: ys)
       | LiftStopped b -> LiftStopped b)
    | LiftStopped b -> LiftStopped b
