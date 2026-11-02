(*
   Z3DagDocument.fst

   The opt-in accounting mode `verified-dag-v1`: binder certificates prepared
   on a checked expression graph while the document is marshaled, and the
   check of a quantifier introduction with the DAG guard.

   `ccache` maps native ids to checked sorts, declarations and graph nodes.
   A native id only locates an earlier entry of this cache, under the
   reflection contract the marshaler already relies on (a native AST is
   retained, and so keeps its id, while the document is marshaled): it never
   decides an equality, and nothing is built from an id the cache does not
   hold. `ccache_ok` (every cached sort, declaration and node valid in the
   invariant graph) is earned by the builders below at each update; their
   lookups and updates are charged to the graph's own Preparation and
   Storage budgets.

   `prepare_certificate` rebuilds a certificate from the cache: each entry's
   formula is the expression stored at the node of its native conclusion,
   its binder sorts those of their native sorts, and it returns that
   certificate with the nodes (`prepared`: `handles_ok`, by construction, in
   an invariant graph). Every step returns `Built`, `Exhausted` with the
   graph phase, or `Invalid` with the input it does not take; a certificate
   that cannot be prepared has no prepared form, its `preparation` records
   why, and the opt-in check leaves it pending.

   `verify_binder_dag` checks a prepared certificate: its entries
   (`check_binder_entries`), its root, then `Z3DagGuard.dag_guard`. Its
   success gives the scope facts of `Z3DagGuardProof.lemma_dag_guard`
   (`lemma_verify_binder_dag`).
*)
module Z3DagDocument

open Z3AstTheory
open Z3UnifiedProof
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module T = Z3CheckedTerms
module CG = Z3CheckedGraph
module G = Z3CheckedGuard
module GP = Z3CheckedGuardProof
module DG = Z3DagGuard
module DGP = Z3DagGuardProof
module BS = Z3BinderScope
module SK = Z3Skolemization

let tu : nat = CS.table_units

(* --- The checked marshaling cache --------------------------------------------------------------- *)

noeq
type ccache_raw = {
  graph: CG.cgraph;
  sorts: I.index_tree CG.csort;
  decls: I.index_tree (I.index_tree CG.cdecl);
  exprs: I.index_tree nat;
}

let sorts_ok (g:CG.cgraph) (t:I.index_tree CG.csort) : prop =
  forall (k:nat). (match I.index_get t k with Some v -> CG.csort_ok g v | None -> True)

let decls_ok (g:CG.cgraph) (t:I.index_tree (I.index_tree CG.cdecl)) : prop =
  forall (k a:nat). (match I.index_get t k with
                     | Some inner -> (match I.index_get inner a with Some d -> CG.decl_ok g d | None -> True)
                     | None -> True)

let exprs_ok (g:CG.cgraph) (t:I.index_tree nat) : prop =
  forall (k:nat). (match I.index_get t k with Some x -> x < CG.node_count g | None -> True)

[@@"opaque_to_smt"]
let caches_ok (c:ccache_raw) : prop = sorts_ok c.graph c.sorts /\ decls_ok c.graph c.decls /\ exprs_ok c.graph c.exprs

let reveal_caches (c:ccache_raw)
  : Lemma (caches_ok c <==> (sorts_ok c.graph c.sorts /\ decls_ok c.graph c.decls /\ exprs_ok c.graph c.exprs))
  = FStar.Pervasives.reveal_opaque (`%caches_ok) (caches_ok c)

let ccache_ok (c:ccache_raw) : prop = CG.graph_inv c.graph /\ caches_ok c

type ccache = c:ccache_raw{ccache_ok c}

let lemma_caches_grow (g g':CG.cgraph) (c:ccache_raw)
  : Lemma (requires CG.cgrows g g' /\ sorts_ok g c.sorts /\ decls_ok g c.decls /\ exprs_ok g c.exprs)
          (ensures sorts_ok g' c.sorts /\ decls_ok g' c.decls /\ exprs_ok g' c.exprs)
  = let s (k:nat) : Lemma (match I.index_get c.sorts k with Some v -> CG.csort_ok g' v | None -> True)
      = match I.index_get c.sorts k with Some v -> CG.lemma_csort_grows g g' v | None -> () in
    let d (k a:nat) : Lemma (match I.index_get c.decls k with
                             | Some inner -> (match I.index_get inner a with Some d -> CG.decl_ok g' d | None -> True)
                             | None -> True)
      = match I.index_get c.decls k with
        | Some inner -> (match I.index_get inner a with Some d -> CG.lemma_decl_grows g g' d | None -> ())
        | None -> () in
    FStar.Classical.forall_intro s;
    FStar.Classical.forall_intro_2 d

let empty_cache : ccache =
  CG.lemma_with_sorts (CG.empty 0 0) CS.empty_table 0 0;
  CS.lemma_initial_state ({ CS.preparation = 0; CS.storage = 0 });
  reveal_caches ({ graph = CG.empty 0 0; sorts = I.Empty; decls = I.Empty; exprs = I.Empty });
  { graph = CG.empty 0 0; sorts = I.Empty; decls = I.Empty; exprs = I.Empty }

(* A fresh allowance, for the certificate being prepared. *)
let with_budget (c:ccache) (prep store:nat) : ccache =
  CG.lemma_budget c.graph prep store;
  reveal_caches c;
  lemma_caches_grow c.graph ({ c.graph with CG.prep = prep; CG.store = store }) c;
  reveal_caches ({ c with graph = { c.graph with CG.prep = prep; CG.store = store } });
  { c with graph = { c.graph with CG.prep = prep; CG.store = store } }

(* `c'` extends `c`: the same graph nodes and expressions, more sorts. *)
let cgrow (c c':ccache) : prop = CG.cgrows c.graph c'.graph

(* Why a preparation step stops: a phase of the graph's own budget is
   exhausted, or its input is one the checked builders do not take (an id the
   cache does not hold, a node that is not earlier). Either leaves the
   certificate without a prepared form, pending. *)
type invalid_reason =
  | MissingExpression
  | MissingSort
  | MissingDeclaration
  | RefusedNode

noeq
type step (a:Type) =
  | Built : value:a -> step a
  | Exhausted : phase:T.phase -> step a
  | Invalid : reason:invalid_reason -> step a

(* The failure of `r`, at another type. *)
let fail (#a #b:Type) (r:step a) : r':step b{~(Built? r')} =
  match r with
  | Exhausted p -> Exhausted p
  | Invalid w -> Invalid w
  | Built _ -> Invalid RefusedNode

(* `prep` and `store` units, from the graph's budgets. *)
let spend (c:ccache) (prep store:nat) : r:step ccache{Built? r ==> cgrow c (Built?.value r)} =
  if c.graph.CG.prep < prep then Exhausted T.Preparation
  else if c.graph.CG.store < store then Exhausted T.Storage
  else begin
    let g' = { c.graph with CG.prep = c.graph.CG.prep - prep; CG.store = c.graph.CG.store - store } in
    CG.lemma_budget c.graph g'.CG.prep g'.CG.store;
    reveal_caches c;
    lemma_caches_grow c.graph g' c;
    reveal_caches ({ c with graph = g' });
    Built ({ c with graph = g' })
  end

(* The graph `g'`, grown from the cache's. *)
let with_graph (c:ccache) (g':CG.cgraph{CG.graph_inv g' /\ CG.cgrows c.graph g'}) : c':ccache{cgrow c c'} =
  reveal_caches c;
  lemma_caches_grow c.graph g' c;
  reveal_caches ({ c with graph = g' });
  { c with graph = g' }

(* --- Lookups by native id ------------------------------------------------------------------------- *)

noeq
type found (a:Type) =
  | Found : cache:ccache -> value:a -> found a
  | Missing : cache:ccache -> found a
  | LookupExhausted

let find_sort (c:ccache) (nid:nat)
  : r:found CG.csort{(Found? r ==> cgrow c (Found?.cache r) /\ CG.csort_ok (Found?.cache r).graph (Found?.value r)) /\
                     (Missing? r ==> cgrow c (Missing?.cache r))} =
  match spend c tu 0 with
  | Built c' -> reveal_caches c'; (match I.index_get c'.sorts nid with Some v -> Found c' v | None -> Missing c')
  | _ -> LookupExhausted

let find_expr (c:ccache) (nid:nat)
  : r:found nat{(Found? r ==> cgrow c (Found?.cache r) /\ Found?.value r < CG.node_count (Found?.cache r).graph) /\
                (Missing? r ==> cgrow c (Missing?.cache r))} =
  match spend c tu 0 with
  | Built c' -> reveal_caches c'; (match I.index_get c'.exprs nid with Some x -> Found c' x | None -> Missing c')
  | _ -> LookupExhausted

(* A lookup that found nothing: `why` if the id is not cached, else the
   exhausted lookup. *)
let not_found (#a #b:Type) (why:invalid_reason) (r:found a) : r':step b{~(Built? r')} =
  match r with
  | LookupExhausted -> Exhausted T.Preparation
  | _ -> Invalid why

let rec lemma_csorts_rev (g:CG.cgraph) (l acc:list CG.csort)
  : Lemma (requires CG.csorts_ok g l /\ CG.csorts_ok g acc) (ensures CG.csorts_ok g (L.rev_acc l acc)) (decreases l)
  = match l with [] -> () | x :: l' -> lemma_csorts_rev g l' (x :: acc)

let rec lemma_below_rev (b:nat) (l acc:list nat)
  : Lemma (requires CS.all_below l b /\ CS.all_below acc b) (ensures CS.all_below (L.rev_acc l acc) b) (decreases l)
  = match l with [] -> () | x :: l' -> lemma_below_rev b l' (x :: acc)

(* The checked sorts of the native sorts `nids`, all cached, in order, after
   `acc`; `c0` is where the lookups started. A self tail call (a loop on the
   Cherry backend): no stack in the number of sorts. *)
let rec find_sorts_from (c0:ccache) (c:ccache{cgrow c0 c}) (nids:list nat) (acc:list CG.csort{CG.csorts_ok c.graph acc})
  : Tot (r:step (ccache & list CG.csort){Built? r ==> (let (c', vs) = Built?.value r in cgrow c0 c' /\ CG.csorts_ok c'.graph vs)})
        (decreases nids) =
  match nids with
  | [] -> lemma_csorts_rev c.graph acc []; Built (c, L.rev acc)
  | n :: rest ->
    let f = find_sort c n in
    (match f with
     | Found c' v ->
       CG.lemma_csorts_grows c.graph c'.graph acc;
       CG.lemma_cgrows_trans c0.graph c.graph c'.graph;
       find_sorts_from c0 c' rest (v :: acc)
     | _ -> not_found MissingSort f)

let find_sorts (c:ccache) (nids:list nat) (acc:list CG.csort{CG.csorts_ok c.graph acc})
  : r:step (ccache & list CG.csort){Built? r ==> (let (c', vs) = Built?.value r in cgrow c c' /\ CG.csorts_ok c'.graph vs)} =
  CG.lemma_cgrows_refl c.graph;
  find_sorts_from c c nids acc

(* The nodes of the native expressions `nids`, all cached, in order, by a
   self tail call. *)
let rec find_exprs_from (c0:ccache) (c:ccache{cgrow c0 c}) (nids:list nat)
                        (acc:list nat{CS.all_below acc (CG.node_count c.graph)})
  : Tot (r:step (ccache & list nat){Built? r ==> (let (c', xs) = Built?.value r in
                                       cgrow c0 c' /\ CS.all_below xs (CG.node_count c'.graph))})
        (decreases nids) =
  match nids with
  | [] -> lemma_below_rev (CG.node_count c.graph) acc []; Built (c, L.rev acc)
  | n :: rest ->
    let f = find_expr c n in
    (match f with
     | Found c' x ->
       T.lemma_all_below_widen acc (CG.node_count c.graph) (CG.node_count c'.graph);
       CG.lemma_cgrows_trans c0.graph c.graph c'.graph;
       find_exprs_from c0 c' rest (x :: acc)
     | _ -> not_found MissingExpression f)

let find_exprs (c:ccache) (nids:list nat) (acc:list nat{CS.all_below acc (CG.node_count c.graph)})
  : r:step (ccache & list nat){Built? r ==> (let (c', xs) = Built?.value r in
                                  cgrow c c' /\ CS.all_below xs (CG.node_count c'.graph))} =
  CG.lemma_cgrows_refl c.graph;
  find_exprs_from c c nids acc

(* --- Building by native id -------------------------------------------------------------------------- *)

let lemma_put_sorts (g:CG.cgraph) (t:I.index_tree CG.csort) (nid:nat) (v:CG.csort)
  : Lemma (requires sorts_ok g t /\ CG.csort_ok g v) (ensures sorts_ok g (I.index_put t nid v))
  = let aux (k:nat) : Lemma (match I.index_get (I.index_put t nid v) k with Some w -> CG.csort_ok g w | None -> True)
      = I.lemma_index_put t nid v k in
    FStar.Classical.forall_intro aux

let put_sort (c:ccache) (nid:nat) (v:CG.csort{CG.csort_ok c.graph v}) : r:step ccache{Built? r ==> cgrow c (Built?.value r)} =
  let r = spend c tu (1 + tu) in
  match r with
  | Built c1 ->
    CG.lemma_csort_grows c.graph c1.graph v;
    reveal_caches c1;
    lemma_put_sorts c1.graph c1.sorts nid v;
    reveal_caches ({ c1 with sorts = I.index_put c1.sorts nid v });
    Built ({ c1 with sorts = I.index_put c1.sorts nid v })
  | _ -> fail r

let lemma_put_exprs (g:CG.cgraph) (t:I.index_tree nat) (nid x:nat)
  : Lemma (requires exprs_ok g t /\ x < CG.node_count g) (ensures exprs_ok g (I.index_put t nid x))
  = let aux (k:nat) : Lemma (match I.index_get (I.index_put t nid x) k with Some y -> y < CG.node_count g | None -> True)
      = I.lemma_index_put t nid x k in
    FStar.Classical.forall_intro aux

let put_expr (c:ccache) (nid:nat) (x:nat{x < CG.node_count c.graph}) : r:step ccache{Built? r ==> cgrow c (Built?.value r)} =
  let r = spend c tu (1 + tu) in
  match r with
  | Built c1 ->
    reveal_caches c1;
    lemma_put_exprs c1.graph c1.exprs nid x;
    reveal_caches ({ c1 with exprs = I.index_put c1.exprs nid x });
    Built ({ c1 with exprs = I.index_put c1.exprs nid x })
  | _ -> fail r

let decl_of (c:ccache) (nid arity:nat) : r:option CG.cdecl{Some? r ==> CG.decl_ok c.graph (Some?.v r)} =
  reveal_caches c;
  match I.index_get c.decls nid with
  | Some inner -> I.index_get inner arity
  | None -> None

let lemma_put_decls (g:CG.cgraph) (t:I.index_tree (I.index_tree CG.cdecl)) (nid arity:nat) (d:CG.cdecl)
  : Lemma (requires decls_ok g t /\ CG.decl_ok g d)
          (ensures decls_ok g (I.index_put t nid (I.index_put (match I.index_get t nid with Some inner -> inner | None -> I.Empty) arity d)))
  = let inner = match I.index_get t nid with Some inner -> inner | None -> I.Empty in
    let t' = I.index_put t nid (I.index_put inner arity d) in
    let aux (k a:nat) : Lemma (match I.index_get t' k with
                               | Some u -> (match I.index_get u a with Some e -> CG.decl_ok g e | None -> True)
                               | None -> True)
      = I.lemma_index_put t nid (I.index_put inner arity d) k;
        I.lemma_index_put inner arity d a in
    FStar.Classical.forall_intro_2 aux

let put_decl (c:ccache) (nid arity:nat) (d:CG.cdecl{CG.decl_ok c.graph d}) : r:step ccache{Built? r ==> cgrow c (Built?.value r)} =
  let r = spend c (2 * tu) (2 + 2 * tu) in
  match r with
  | Built c1 ->
    CG.lemma_decl_grows c.graph c1.graph d;
    reveal_caches c1;
    lemma_put_decls c1.graph c1.decls nid arity d;
    let inner = match I.index_get c1.decls nid with Some inner -> inner | None -> I.Empty in
    reveal_caches ({ c1 with decls = I.index_put c1.decls nid (I.index_put inner arity d) });
    Built ({ c1 with decls = I.index_put c1.decls nid (I.index_put inner arity d) })
  | _ -> fail r

let build_base_sort (c:ccache) (nid:nat) (name:string) : step ccache =
  match CG.base_sort c.graph name with
  | CG.Sorted g' v -> CG.lemma_base_sort c.graph name; let c1 = with_graph c g' in put_sort c1 nid v
  | CG.SortExhausted p -> Exhausted p

let build_array_sort (c:ccache) (nid:nat) (dom:list nat) (range:nat) : step ccache =
  let fs = find_sorts c dom [] in
  match fs with
  | Built (c1, ds) ->
    let f = find_sort c1 range in
    (match f with
     | Found c2 r ->
       CG.lemma_csorts_grows c1.graph c2.graph ds;
       CG.lemma_array_sort c2.graph ds r;
       (match CG.array_sort c2.graph ds r with
        | CG.Sorted g' v -> put_sort (with_graph c2 g') nid v
        | CG.SortExhausted p -> Exhausted p)
     | _ -> not_found MissingSort f)
  | _ -> fail fs

let build_var (c:ccache) (nid:nat) (n:nat) (sort:nat) : step ccache =
  let f = find_sort c sort in
  match f with
  | Found c1 v ->
    CG.lemma_add_var c1.graph n v;
    (match CG.add_var c1.graph n v with
     | CG.Built g' x -> put_expr (with_graph c1 g') nid x
     | CG.BuildExhausted p -> Exhausted p
     | CG.BuildInvalid -> Invalid RefusedNode)
  | _ -> not_found MissingSort f

noeq
type with_decl = { wcache: ccache; wdecl: CG.cdecl }

let decl_ok_from (c:ccache) (r:with_decl) : prop = cgrow c r.wcache /\ CG.decl_ok r.wcache.graph r.wdecl

let decl_from_sort (c:ccache) (dnid arity:nat) (name:string) (tag:option decl_kind) (params:list int) (xs:list nat)
                   (r:CG.csort{CG.csort_ok c.graph r})
  : r:step with_decl{Built? r ==> decl_ok_from c (Built?.value r)} =
  CG.lemma_new_decl c.graph name tag params xs r;
  match CG.new_decl c.graph name tag params xs r with
  | CG.Declared g' d ->
    let c3 = with_graph c g' in
    let pr = put_decl c3 dnid arity d in
    (match pr with
     | Built c4 ->
       CG.lemma_decl_grows c3.graph c4.graph d;
       CG.lemma_cgrows_trans c.graph c3.graph c4.graph;
       Built ({ wcache = c4; wdecl = d })
     | _ -> fail pr)
  | CG.DeclExhausted p -> Exhausted p
  | CG.DeclInvalid -> Invalid RefusedNode

let make_decl (c:ccache) (dnid arity:nat) (name:string) (tag:option decl_kind) (params:list int) (xs:list nat)
              (range:nat)
  : r:step with_decl{Built? r ==> decl_ok_from c (Built?.value r)} =
  match CS.checked_name_units name c.graph.CG.prep with
  | None -> Exhausted T.Preparation
  | Some len ->
    let sp = spend c (len + L.length params) 0 in
    (match sp with
     | Built c1 ->
       let f = find_sort c1 range in
       (match f with
        | Found c2 r ->
          CG.lemma_cgrows_trans c.graph c1.graph c2.graph;
          let res = decl_from_sort c2 dnid arity name tag params xs r in
          if not (Built? res) then fail res
          else begin
            let c3 = (Built?.value res).wcache in
            let d = (Built?.value res).wdecl in
            CG.lemma_cgrows_trans c.graph c2.graph c3.graph;
            Built ({ wcache = c3; wdecl = d })
          end
        | _ -> not_found MissingSort f)
     | _ -> fail sp)

(* The declaration `dnid` at the arity of `xs`, cached, or made from the
   argument nodes and its range (its name's characters counted, bounded). *)
let ensure_decl (c:ccache) (dnid:nat) (name:string) (tag:option decl_kind) (params:list int) (xs:list nat)
                (range:nat) : r:step with_decl{Built? r ==> decl_ok_from c (Built?.value r)} =
  let arity = L.length xs in
  let sp = spend c (2 * tu) 0 in
  match sp with
  | Built c0 ->
    (match decl_of c0 dnid arity with
     | Some d -> Built ({ wcache = c0; wdecl = d })
     | None ->
       let res = make_decl c0 dnid arity name tag params xs range in
       if not (Built? res) then fail res
       else begin
         let c1 = (Built?.value res).wcache in
         let d = (Built?.value res).wdecl in
         CG.lemma_cgrows_trans c.graph c0.graph c1.graph;
         Built ({ wcache = c1; wdecl = d })
       end)
  | _ -> fail sp

let build_app (c:ccache) (nid:nat) (dnid:nat) (name:string) (tag:option decl_kind) (params:list int)
              (args:list nat) (range:nat) : step ccache =
  let fs = find_exprs c args [] in
  match fs with
  | Built (c1, xs) ->
    let res = ensure_decl c1 dnid name tag params xs range in
    (match res with
     | Built p ->
       let c2 = p.wcache in
       let d = p.wdecl in
       CG.lemma_add_app c2.graph d xs;
       (match CG.add_app c2.graph d xs with
        | CG.Built g' x -> put_expr (with_graph c2 g') nid x
        | CG.BuildExhausted ph -> Exhausted ph
        | CG.BuildInvalid -> Invalid RefusedNode)
     | _ -> fail res)
  | _ -> fail fs

let build_quant (c:ccache) (nid:nat) (k:quantifier_kind) (sorts:list nat) (body:nat) : step ccache =
  let fs = find_sorts c sorts [] in
  match fs with
  | Built (c1, bs) ->
    let f = find_expr c1 body in
    (match f with
     | Found c2 y ->
       CG.lemma_csorts_grows c1.graph c2.graph bs;
       CG.lemma_add_quant c2.graph k bs y;
       (match CG.add_quant c2.graph k bs y with
        | CG.Built g' x -> put_expr (with_graph c2 g') nid x
        | CG.BuildExhausted p -> Exhausted p
        | CG.BuildInvalid -> Invalid RefusedNode)
     | _ -> not_found MissingExpression f)
  | _ -> fail fs

(* --- Prepared certificates ------------------------------------------------------------------------ *)

(* A binder entry as marshaled: its native conclusion and binder sorts. *)
type raw_entry = {
  raw_name: string;
  raw_formula: nat;
  raw_premises: list int;
  raw_sorts: option (list nat);
}

noeq
type companion = {
  pgraph: CG.cgraph;
  pcert: binder_certificate;
  phandles: list nat;
}

type prepared = p:companion{CG.graph_inv p.pgraph /\ DGP.handles_ok p.pgraph p.pcert.binder_entries p.phandles}

let entry_ok (g:CG.cgraph) (e:binder_entry) (h:nat) : prop = h < CG.node_count g /\ CG.value_of g h == Some e.binder_formula

let rec lemma_handles_rev (g:CG.cgraph) (es:list binder_entry) (hs:list nat) (ae:list binder_entry) (ah:list nat)
  : Lemma (requires DGP.handles_ok g es hs /\ DGP.handles_ok g ae ah)
          (ensures DGP.handles_ok g (L.rev_acc es ae) (L.rev_acc hs ah)) (decreases es)
  = match es, hs with
    | e :: es', h :: hs' -> lemma_handles_rev g es' hs' (e :: ae) (h :: ah)
    | _, _ -> ()

let rec lemma_handles_grow (g g':CG.cgraph) (es:list binder_entry) (hs:list nat)
  : Lemma (requires CG.cgrows g g' /\ DGP.handles_ok g es hs) (ensures DGP.handles_ok g' es hs) (decreases es)
  = match es, hs with
    | _ :: es', _ :: hs' -> lemma_handles_grow g g' es' hs'
    | _, _ -> ()

let value_at (g:CG.cgraph) (x:nat{CG.graph_inv g /\ x < CG.node_count g}) : e:expr{CG.value_of g x == Some e} =
  CG.reveal_exact g x;
  match CG.value_of g x with Some e -> e

(* The entries of `raw`, rebuilt from the cache, last first in `ae`/`ah`. *)
noeq
type entries_of = { ecache: ccache; eentries: list binder_entry; ehandles: list nat }

noeq
type sorts_of = { scache: ccache; ssorts: option (list sort) }

(* The entries of `raw` after `ae`/`ah`, rebuilt from the cache; `c0` is
   where the rebuilding started. A self tail call: no stack in the number of
   entries. *)
let rec prepare_entries_from (c0:ccache) (c:ccache{cgrow c0 c}) (raw:list raw_entry) (ae:list binder_entry) (ah:list nat)
  : Tot (r:step entries_of{Built? r ==> (let e = Built?.value r in cgrow c0 e.ecache /\ DGP.handles_ok e.ecache.graph e.eentries e.ehandles)})
        (requires DGP.handles_ok c.graph ae ah)
        (decreases raw) =
  match raw with
  | [] ->
    lemma_handles_rev c.graph ae ah [] [];
    Built ({ ecache = c; eentries = L.rev ae; ehandles = L.rev ah })
  | r :: rest ->
    let fe = find_expr c r.raw_formula in
    (match fe with
     | Found c1 x ->
       let f = value_at c1.graph x in
       let sorts : s:step sorts_of{Built? s ==> cgrow c1 (Built?.value s).scache} =
         match r.raw_sorts with
         | None -> CG.lemma_cgrows_refl c1.graph; Built ({ scache = c1; ssorts = None })
         | Some nids ->
           let fs = find_sorts c1 nids [] in
           (match fs with
            | Built (c2, cs) -> Built ({ scache = c2; ssorts = Some (L.map fst cs) })
            | _ -> fail fs) in
       (match sorts with
        | Built so ->
          let c2 = so.scache in
          let bs = so.ssorts in
          let e = { binder_name = r.raw_name; binder_formula = f; binder_premises = r.raw_premises; binder_sorts = bs } in
          lemma_handles_grow c.graph c2.graph ae ah;
          CG.lemma_cgrows_trans c.graph c1.graph c2.graph;
          CG.lemma_cgrows_trans c0.graph c.graph c2.graph;
          prepare_entries_from c0 c2 rest (e :: ae) (x :: ah)
        | _ -> fail sorts)
     | _ -> not_found MissingExpression fe)

let prepare_certificate (c:ccache) (raw:list raw_entry) (root:int) : step (ccache & prepared) =
  CG.lemma_cgrows_refl c.graph;
  let r = prepare_entries_from c c raw [] [] in
  match r with
  | Built e ->
    let c' = e.ecache in
    let es = e.eentries in
    let hs = e.ehandles in
    Built (c', { pgraph = c'.graph; pcert = { binder_entries = es; binder_root = root }; phandles = hs })
  | _ -> fail r

(* Why a quantifier introduction of an opt-in document has no prepared
   certificate: its preparation stopped (a graph phase exhausted, or an input
   the builders do not take), its document is clausal (whose entries are
   renumbered when it is pruned), its document has definitions (whose
   expansion changes the certificate after it was prepared: the prepared one
   is not the one the default checks), or no preparation was recorded for it. *)
type unprepared_reason =
  | UnpreparedExhausted : phase:T.phase -> unprepared_reason
  | UnpreparedInvalid : reason:invalid_reason -> unprepared_reason
  | UnpreparedClausal
  | UnpreparedDefinitions
  | UnpreparedAbsent

let reason_of (#a:Type) (r:step a) : unprepared_reason =
  match r with
  | Exhausted p -> UnpreparedExhausted p
  | Invalid w -> UnpreparedInvalid w
  | Built _ -> UnpreparedAbsent

(* A lookup in the cache that its budget no longer pays. *)
let lookup_exhausted : unprepared_reason = UnpreparedExhausted T.Preparation

(* The preparation of one quantifier introduction: its prepared certificate,
   or why there is none with the graph units (preparation, storage) that the
   steps before the one that stopped used of the certificate's allowance. *)
noeq
type preparation =
  | Ready : p:prepared -> preparation
  | Unready : reason:unprepared_reason -> used:option (nat & nat) -> preparation

(* The preparations of a document's quantifier introductions, by entry. *)
noeq
type companions = {
  clausal: bool;
  preparations: I.index_tree preparation;
}

let no_companions : companions = { clausal = false; preparations = I.Empty }

let preparation_of (cs:companions) (i:nat) : preparation =
  if cs.clausal then Unready UnpreparedClausal None
  else match I.index_get cs.preparations i with
    | Some p -> p
    | None -> Unready UnpreparedAbsent None

(* --- The check -------------------------------------------------------------------------------------- *)

(* The budgets of the experimental opt-in mode, in shares: a certificate with
   `n` entries gets `n + 1` of each. Calibrated on the NNF task's 20 diagnosed
   guard-budget certificates (28 dumps, PulseCore.Action-1 query 1 node 433
   among them; OCAML_CHECKER_REPORT.md): each is the smallest power of two at
   least 1.2 times the largest units per share measured in its phase (graph
   preparation 9,191, graph storage 2,071, guard validation 50,188, guard
   storage 9,557), except the guard's preparation. That one only counts the
   names of binder sorts again (largest 25 per share measured) and allows
   16,384 per share, as the graph's preparation does, so that a binder sort
   name of a few thousand characters is still checked (the CLI regression's
   1,000-character name). These are the mode's budgets, not the default
   checker's, which never selects the mode and keeps `binder_work_limit`.

   The checked graph's allowance while a certificate is marshaled: *)
let graph_preparation_per_entry : nat = 16384
let graph_storage_per_entry : nat = 4096

(* the DAG guard's: *)
let dag_preparation_per_entry : nat = 16384
let dag_validation_per_entry : nat = 65536
let dag_storage_per_entry : nat = 16384

let dag_budget (n:nat) : G.resource_budget = {
  G.preparation = dag_preparation_per_entry * (n + 1);
  G.validation = dag_validation_per_entry * (n + 1);
  G.storage = dag_storage_per_entry * (n + 1);
}

(* The units the checked graph spent on a prepared certificate, of its allowance. *)
let graph_used (p:prepared) : nat & nat =
  let shares = count_cells 0 p.pcert.binder_entries + 1 in
  let gp = graph_preparation_per_entry * shares in
  let gs = graph_storage_per_entry * shares in
  ((if p.pgraph.CG.prep <= gp then gp - p.pgraph.CG.prep else 0),
   (if p.pgraph.CG.store <= gs then gs - p.pgraph.CG.store else 0))

let verify_binder_dag (skolems:list SK.definition) (assertions:list judgment) (p:prepared) (concl:judgment)
  : G.binder_outcome =
  let c = p.pcert in
  match check_binder_entries skolems assertions c.binder_entries I.Empty 0 with
  | None -> G.BinderEntriesFailed
  | Some cache ->
    if I.index_find cache c.binder_root <> Some concl then G.BinderEntriesFailed
    else
      let n = count_cells 0 c.binder_entries in
      let b = dag_budget n in
      match DG.dag_guard b p.pgraph c cache p.phandles with
      | DG.DagChecked ds -> G.BinderGuardChecked (G.left_of ds.DG.gs)
      | DG.DagRefused -> G.BinderGuardRefused b
      | DG.DagExhausted ph -> G.BinderGuardExhausted ph

let lemma_verify_binder_dag (skolems:list SK.definition) (assertions:list judgment) (p:prepared) (concl:judgment)
  : Lemma (requires G.BinderGuardChecked? (verify_binder_dag skolems assertions p concl))
          (ensures (let c = p.pcert in
                    Some? (check_binder_entries skolems assertions c.binder_entries I.Empty 0) /\
                    (let cache = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
                     I.index_find cache c.binder_root == Some concl /\
                     (exists (t:scope_demands).
                       0 <= c.binder_root /\ c.binder_root < L.length c.binder_entries /\
                       L.memP [] (scope_demanded t c.binder_root) /\ BS.entries_scoped t cache 0 c.binder_entries))))
  = let c = p.pcert in
    let cache = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
    DGP.lemma_check_entries_classified skolems assertions c.binder_entries I.Empty 0;
    let n = count_cells 0 c.binder_entries in
    DGP.lemma_dag_guard (dag_budget n) p.pgraph c cache p.phandles

(* `check_node_with_membership` with the DAG guard for quantifier
   introductions, on the prepared certificate of the node (`p`); a node
   without one stays pending. Every other node is checked by it. *)
let check_node_dag (skolems:list SK.definition) (strict:bool) (assertions:list judgment)
                   (contains:judgment -> bool) (node:proof_node) (p:option prepared)
  : option (checked_fact & nat) & option G.binder_outcome =
  match node.kind with
  | QuantifierIntroduction _ ->
    let facts = premise_judgments node.premises in
    if well_formed node.conclusion && judgments_wf facts && scopes_wf node.premises &&
       facts = [] && Some? (relational node.conclusion)
    then
      let outcome = match p with
        | Some p -> verify_binder_dag skolems assertions p node.conclusion
        | None -> G.BinderUnprepared in
      Some ({ conclusion = node.conclusion; hypotheses = [] }, (if G.BinderGuardChecked? outcome then 0 else 1)),
      Some outcome
    else None, None
  | _ -> check_node_with_membership skolems strict assertions contains node, None

(* The opt-in node check differs from the default only in what decides a
   quantifier introduction's pending count: the DAG check of its prepared
   certificate. *)
let lemma_check_node_dag (skolems:list SK.definition) (strict:bool) (assertions:list judgment)
                         (contains:judgment -> bool) (node:proof_node) (p:option prepared)
  : Lemma (fst (check_node_dag skolems strict assertions contains node p) ==
           (match check_node_with_membership skolems strict assertions contains node, node.kind with
            | Some (fact, _), QuantifierIntroduction _ ->
              Some (fact, (match p with
                           | Some p -> if G.BinderGuardChecked? (verify_binder_dag skolems assertions p node.conclusion)
                                       then 0 else 1
                           | None -> 1))
            | r, _ -> r))
  = ()
