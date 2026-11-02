(*
   Z3DagGuardProof.fst

   What the opt-in `verified-dag-v1` guard (`Z3DagGuard.dag_guard`) earns.

   * `lemma_dag_guard`: on an invariant marshaled graph, with one node per
     entry that stores exactly the entry's formula (`handles_ok`) and a cache
     holding each entry's classified formula (`cache_classified`, which the
     checker's own cache satisfies, `lemma_check_entries_classified`), a
     `DagChecked` result establishes the root as an entry demanded at `[]`
     and `Z3BinderScope.entries_scoped` for the demand table its ids denote:
     the specification of the old guard's success
     (`Z3BinderScope.lemma_guard`) and of `verified-sorts-v1`
     (`Z3CheckedGuardProof.lemma_verified_guard`).
   * The scope facts come from the memo of `Z3DagScope` (`memo_ok`): every
     recorded node/scope pair is `Z3Definitions.scoped` of what the pair
     denotes. Facts are structural, about the stored expressions; no semantic
     fact is recorded or reused.
*)
module Z3DagGuardProof

open Z3AstTheory
open Z3UnifiedProof
open Z3DagGuard
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module T = Z3CheckedTerms
module W = Z3CheckedScope
module G = Z3CheckedGuard
module GP = Z3CheckedGuardProof
module CG = Z3CheckedGraph
module DS = Z3DagScope
module BS = Z3BinderScope
module D = Z3Definitions
module SK = Z3Skolemization

(* --- The entries' nodes and the checker's cache ------------------------------------------------- *)

noextract
let rec handles_ok (cg:CG.cgraph) (entries:list binder_entry) (handles:list nat) : Tot prop (decreases entries) =
  match entries, handles with
  | [], [] -> True
  | e :: rest, h :: hs -> h < CG.node_count cg /\ CG.value_of cg h == Some e.binder_formula /\ handles_ok cg rest hs
  | _, _ -> False

noextract
let rec cache_classified (cache:I.index_tree judgment) (k:nat) (entries:list binder_entry)
  : Tot prop (decreases entries) =
  match entries with
  | [] -> True
  | e :: rest -> I.index_find cache k == classify_fact e.binder_formula /\ cache_classified cache (k + 1) rest

let rec lemma_check_entries_classified (skolems:list SK.definition) (assertions:list judgment)
                                       (entries:list binder_entry) (cache:I.index_tree judgment) (next:nat)
  : Lemma (ensures (match check_binder_entries skolems assertions entries cache next with
                    | Some cache' ->
                      cache_classified cache' next entries /\
                      (forall (q:nat). q < next ==> I.index_find cache' q == I.index_find cache q)
                    | None -> True))
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      (match classify_fact e.binder_formula with
       | Some concl ->
         let cache1 = I.index_put cache next concl in
         lemma_check_entries_classified skolems assertions rest cache1 (next + 1);
         let aux (q:nat) : Lemma (I.index_find cache1 q == (if q = next then Some concl else I.index_find cache q))
           = I.lemma_index_put cache next concl q in
         FStar.Classical.forall_intro aux
       | None -> ())

(* An entry's judgment is its formula or the formula's two arguments. *)
let lemma_classified_shape (f:expr) (j:judgment)
  : Lemma (requires classify_fact f == Some j)
          (ensures (match j with
                    | Holds e -> e == f
                    | Equal a b | Observational a b ->
                      (match f with App _ [x; y] -> x == a /\ y == b | _ -> False)))
  = match f with
    | App d [x; y] ->
      (match Z3ObservationalEquality.is_oeq f with
       | Some (p, q) -> assert (p == x /\ q == y)
       | None -> ())
    | _ -> ()

let rec lemma_values_view (cg cg':CG.cgraph) (xs:list nat)
  : Lemma (requires cg'.CG.values == cg.CG.values) (ensures CG.values_of cg' xs == CG.values_of cg xs) (decreases xs)
  = match xs with [] -> () | _ :: rest -> lemma_values_view cg cg' rest

let lemma_judgment_nodes (cg:CG.cgraph) (h:nat) (f:expr) (j:judgment)
  : Lemma (requires CG.graph_inv cg /\ h < CG.node_count cg /\ CG.value_of cg h == Some f /\ classify_fact f == Some j)
          (ensures (match judgment_nodes cg h j with
                    | Some xs -> CS.all_below xs (CG.node_count cg) /\ CG.values_of cg xs == Some (G.judgment_exprs j)
                    | None -> True))
  = lemma_classified_shape f j;
    CG.reveal_exact cg h;
    match j with
    | Holds _ -> ()
    | _ ->
      (match CG.node_of cg h, CG.value_of cg h with
       | Some (T.ENApp _ xs _), Some (App _ args) -> T.lemma_all_below_widen xs h (CG.node_count cg)
       | _, _ -> ())

(* --- The marshaled graph read with the guard's sort table ----------------------------------------- *)

let lemma_view (cg:CG.cgraph) (t:CS.sort_table)
  : Lemma (requires CG.graph_inv cg /\ CS.valid_table t /\ T.table_grows cg.CG.terms.T.sorts t)
          (ensures CG.graph_inv (CG.with_sorts cg t 0 0) /\ CG.cgrows cg (CG.with_sorts cg t 0 0))
  = CG.lemma_with_sorts cg t 0 0

let lemma_view_grows (cg:CG.cgraph) (t t':CS.sort_table)
  : Lemma (requires T.table_grows t t') (ensures CG.cgrows (CG.with_sorts cg t 0 0) (CG.with_sorts cg t' 0 0))
  = ()

(* The forward pass's invariant: the old guard's (`fwd`), the view of the
   marshaled graph invariant, and the scope ids and memo valid in it. *)
let dinv (cg:CG.cgraph) (t1:CS.sort_table) (td:G.id_demands) (ds:dstate) : prop =
  GP.fwd t1 td ds.gs /\ CG.graph_inv cg /\ T.table_grows cg.CG.terms.T.sorts ds.gs.G.graph.T.sorts /\
  CG.graph_inv (view cg ds) /\ DS.scopes_ok ds.scopes (CG.sort_count (view cg ds)) /\
  DS.memo_ok (view cg ds) ds.scopes ds.memo

(* --- One demanded scope ------------------------------------------------------------------------------ *)

let lemma_scope_sorts (cg:CG.cgraph) (ds:dstate) (sc:DS.scope_table) (sid:nat) (s:list nat)
  : Lemma (requires DS.scope_ids sc sid == s)
          (ensures DS.scope_sorts (view cg ds) sc sid == GP.interp_scope ds.gs.G.graph.T.sorts s)
  = ()

(* The walk part: the judgment is scoped at the scope `s` denotes. *)
let lemma_scope_walk (cg:CG.cgraph) (t1:CS.sort_table) (td:G.id_demands) (ds:dstate) (xs:list nat) (j:judgment)
                     (s:list nat) (v store:nat)
  : Lemma (requires dinv cg t1 td ds /\ CS.all_below xs (CG.node_count cg) /\
                    CG.values_of cg xs == Some (G.judgment_exprs j) /\
                    CS.all_below s ds.gs.G.graph.T.sorts.CS.node_count)
          (ensures (match DS.intern_scope ds.scopes s v store with
                    | DS.Pushed sc sid v1 s1 ->
                      (match DS.walk (view cg ds) sc ds.memo v1 s1 (DS.visits xs sid []) with
                       | DS.Walked sc' m' v2 _ ->
                         DS.scopes_ok sc' (CG.sort_count (view cg ds)) /\ DS.memo_ok (view cg ds) sc' m' /\
                         (match DS.all_recorded m' xs sid v2 with
                          | Some (true, _) -> BS.binder_judgment_scoped (GP.interp_scope ds.gs.G.graph.T.sorts s) j
                          | _ -> True)
                       | _ -> True)
                    | DS.PushExhausted _ -> True))
  = let g = view cg ds in
    let bound = CG.sort_count g in
    DS.lemma_intern_scope ds.scopes bound s v store;
    match DS.intern_scope ds.scopes s v store with
    | DS.Pushed sc sid v1 s1 ->
      CG.lemma_cgrows_refl g;
      DS.lemma_memo_grows g g ds.scopes sc ds.memo;
      DS.lemma_visits_below xs sid [] sc.DS.count;
      DS.lemma_walk g sc ds.memo v1 s1 (DS.visits xs sid []);
      (match DS.walk g sc ds.memo v1 s1 (DS.visits xs sid []) with
       | DS.Walked sc' m' v2 _ ->
         (match DS.all_recorded m' xs sid v2 with
          | Some (true, _) ->
            lemma_values_view cg g xs;
            DS.lemma_recorded g sc' m' xs sid v2;
            DS.lemma_scope_ids_grow sc sc' sid;
            lemma_scope_sorts cg ds sc' sid s;
            GP.lemma_judgment_scoped (GP.interp_scope ds.gs.G.graph.T.sorts s) j
          | _ -> ())
       | _ -> ())
    | _ -> ()

let lemma_scope_checked (cg:CG.cgraph) (t1:CS.sort_table) (td:G.id_demands) (ds:dstate) (k:int) (e:binder_entry)
                        (bids:option (list nat)) (xs:list nat) (j:judgment) (s:list nat)
  : Lemma (requires dinv cg t1 td ds /\ GP.premise_ids_ok ds.gs.G.graph.T.sorts e bids /\
                    CS.all_below xs (CG.node_count cg) /\ CG.values_of cg xs == Some (G.judgment_exprs j) /\
                    CS.all_below s t1.CS.node_count /\ DGo? (scope_checked cg ds k bids e.binder_premises xs s))
          (ensures (let DGo ds' = scope_checked cg ds k bids e.binder_premises xs s in
                    dinv cg t1 td ds' /\ ds'.gs.G.graph == ds.gs.G.graph /\
                    BS.binder_judgment_scoped (GP.interp_scope t1 s) j /\
                    BS.premises_demanded (GP.interp_demands t1 td) k e.binder_premises
                      (BS.premise_scope_of e (GP.interp_scope t1 s))))
  = let gt = ds.gs.G.graph.T.sorts in
    T.lemma_all_below_widen s t1.CS.node_count gt.CS.node_count;
    CS.lemma_map_agree t1 gt t1.CS.node_count s;
    W.lemma_count_within ds.gs.G.valid 0 s;
    let Some (len, v) = W.count_within ds.gs.G.valid 0 s in
    lemma_scope_walk cg t1 td ds xs j s v ds.gs.G.store;
    let DS.Pushed sc sid v1 s1 = DS.intern_scope ds.scopes s v ds.gs.G.store in
    let DS.Walked sc' m' v2 s2 = DS.walk (view cg ds) sc ds.memo v1 s1 (DS.visits xs sid []) in
    let Some (true, v3) = DS.all_recorded m' xs sid v2 in
    let gs1 = { ds.gs with G.valid = v3; G.store = s2 } in
    GP.lemma_premise_scope gs1 e bids s len;
    let G.Go (s', _) gs2 = G.premise_scope gs1 bids s len in
    GP.lemma_premises_checked t1 td gs2 k e.binder_premises s';
    let G.Go () gs3 = G.premises_checked gs2 k e.binder_premises s' in
    assert (gs1.G.graph == ds.gs.G.graph /\ gs2.G.graph == gs1.G.graph /\ gs3.G.graph == gs2.G.graph);
    let ds' = { gs = gs3; scopes = sc'; memo = m' } in
    assert (scope_checked cg ds k bids e.binder_premises xs s == DGo ds');
    assert (view cg ds' == view cg ds);
    assert (GP.fwd t1 td gs3)

let rec lemma_entry_checked (cg:CG.cgraph) (t1:CS.sort_table) (td:G.id_demands) (ds:dstate) (k:int) (e:binder_entry)
                            (bids:option (list nat)) (xs:list nat) (j:judgment) (scopes:list (list nat))
  : Lemma (requires dinv cg t1 td ds /\ GP.premise_ids_ok ds.gs.G.graph.T.sorts e bids /\
                    CS.all_below xs (CG.node_count cg) /\ CG.values_of cg xs == Some (G.judgment_exprs j) /\
                    GP.scopes_below scopes t1.CS.node_count /\
                    DGo? (entry_checked cg ds k bids e.binder_premises xs scopes))
          (ensures (let DGo ds' = entry_checked cg ds k bids e.binder_premises xs scopes in
                    dinv cg t1 td ds' /\ ds'.gs.G.graph == ds.gs.G.graph /\
                    BS.entry_scoped (GP.interp_demands t1 td) k e j (GP.interp_scopes t1 scopes)))
          (decreases scopes)
  = match scopes with
    | [] -> ()
    | s :: rest ->
      lemma_scope_checked cg t1 td ds k e bids xs j s;
      let DGo ds1 = scope_checked cg ds k bids e.binder_premises xs s in
      lemma_entry_checked cg t1 td ds1 k e bids xs j rest

(* --- One entry ------------------------------------------------------------------------------------- *)

(* The guard's sort table grew: the view and every recorded fact carry over. *)
let lemma_dinv_sorts (cg:CG.cgraph) (t1:CS.sort_table) (td:G.id_demands) (ds:dstate) (gs':G.gstate)
  : Lemma (requires dinv cg t1 td ds /\ GP.inv gs' /\ GP.grows ds.gs gs' /\ gs'.G.demands == td)
          (ensures dinv cg t1 td ({ ds with gs = gs' }))
  = let ds' = { ds with gs = gs' } in
    let t = ds.gs.G.graph.T.sorts in
    let t' = gs'.G.graph.T.sorts in
    GP.lemma_fwd_grows t1 td ds.gs gs';
    T.lemma_table_grows_trans cg.CG.terms.T.sorts t t';
    lemma_view cg t';
    lemma_view_grows cg t t';
    DS.lemma_scopes_widen ds.scopes t.CS.node_count t'.CS.node_count;
    DS.lemma_memo_grows (view cg ds) (view cg ds') ds.scopes ds.scopes ds.memo

let lemma_entry_step (cg:CG.cgraph) (t1:CS.sort_table) (td:G.id_demands) (ds:dstate) (k:nat) (e:binder_entry)
                     (j:judgment) (h:nat) (scopes:list (list nat))
  : Lemma (requires dinv cg t1 td ds /\ GP.scopes_below scopes t1.CS.node_count /\
                    (h < CG.node_count cg ==> CG.value_of cg h == Some e.binder_formula) /\
                    classify_fact e.binder_formula == Some j /\ DGo? (entry_step cg ds k e j h scopes))
          (ensures (let DGo ds' = entry_step cg ds k e j h scopes in
                    dinv cg t1 td ds' /\ BS.entry_scoped (GP.interp_demands t1 td) k e j (GP.interp_scopes t1 scopes)))
  = let Some gs0 = G.spend_valid ds.gs (1 + CS.table_units) in
    let ds0 = { ds with gs = gs0 } in
    T.lemma_graph_grows_refl ds.gs.G.graph;
    lemma_dinv_sorts cg t1 td ds gs0;
    lemma_judgment_nodes cg h e.binder_formula j;
    let Some xs = judgment_nodes cg h j in
    GP.lemma_entry_binders gs0 e;
    let G.Go bids gs1 = G.entry_binders gs0 e in
    lemma_dinv_sorts cg t1 td ds0 gs1;
    lemma_entry_checked cg t1 td ({ ds0 with gs = gs1 }) k e bids xs j scopes

let lemma_entries_unfold (cg:CG.cgraph) (ds:dstate) (cache:I.index_tree judgment) (k:nat) (e:binder_entry)
                         (rest:list binder_entry) (h:nat) (hs:list nat) (gs0:G.gstate) (j:judgment)
  : Lemma (requires G.spend_valid ds.gs (1 + CS.table_units) == Some gs0 /\ I.index_find cache k == Some j)
          (ensures entries_checked cg ds cache k (e :: rest) (h :: hs) ==
                   (match G.id_demanded gs0.G.demands k with
                    | [] -> entries_checked cg ({ ds with gs = gs0 }) cache (k + 1) rest hs
                    | scopes ->
                      (match entry_step cg ({ ds with gs = gs0 }) k e j h scopes with
                       | DGo ds1 -> entries_checked cg ds1 cache (k + 1) rest hs
                       | DStop f -> DStop f)))
  = ()

let lemma_entries_scoped_cons (t:scope_demands) (cache:I.index_tree judgment) (k:nat) (e:binder_entry)
                              (rest:list binder_entry) (j:judgment)
  : Lemma (requires I.index_find cache k == Some j /\ BS.entry_scoped t k e j (scope_demanded t k) /\
                    BS.entries_scoped t cache (k + 1) rest)
          (ensures BS.entries_scoped t cache k (e :: rest))
  = ()

let rec lemma_entries_checked (cg:CG.cgraph) (t1:CS.sort_table) (td:G.id_demands) (ds:dstate)
                              (cache:I.index_tree judgment) (k:nat) (entries:list binder_entry) (handles:list nat)
  : Lemma (requires dinv cg t1 td ds /\ handles_ok cg entries handles /\ cache_classified cache k entries /\
                    DGo? (entries_checked cg ds cache k entries handles))
          (ensures (let DGo ds' = entries_checked cg ds cache k entries handles in
                    dinv cg t1 td ds' /\ BS.entries_scoped (GP.interp_demands t1 td) cache k entries))
          (decreases entries)
  = match entries, handles with
    | [], [] -> ()
    | e :: rest, h :: hs ->
      let Some gs0 = G.spend_valid ds.gs (1 + CS.table_units) in
      let ds0 = { ds with gs = gs0 } in
      T.lemma_graph_grows_refl ds.gs.G.graph;
      lemma_dinv_sorts cg t1 td ds gs0;
      let Some j = I.index_find cache k in
      lemma_entries_unfold cg ds cache k e rest h hs gs0 j;
      let t = GP.interp_demands t1 td in
      GP.lemma_demanded t1 td k;
      assert (gs0.G.demands == td);
      (match G.id_demanded td k with
       | [] ->
         lemma_entries_checked cg t1 td ds0 cache (k + 1) rest hs;
         lemma_entries_scoped_cons t cache k e rest j
       | scopes ->
         lemma_entry_step cg t1 td ds0 k e j h scopes;
         let DGo ds1 = entry_step cg ds0 k e j h scopes in
         lemma_entries_checked cg t1 td ds1 cache (k + 1) rest hs;
         lemma_entries_scoped_cons t cache k e rest j)

(* --- The guard ------------------------------------------------------------------------------------- *)

let lemma_initial (budget:G.resource_budget) (cg:CG.cgraph)
  : Lemma (requires CG.graph_inv cg)
          (ensures GP.inv (initial budget cg) /\ (initial budget cg).G.demands == I.Empty /\
                   (initial budget cg).G.graph.T.sorts == cg.CG.terms.T.sorts)
  = GP.lemma_demands_empty cg.CG.terms.T.sorts.CS.node_count

let lemma_start (cg:CG.cgraph) (gs2:G.gstate)
  : Lemma (requires CG.graph_inv cg /\ GP.inv gs2 /\ T.table_grows cg.CG.terms.T.sorts gs2.G.graph.T.sorts)
          (ensures dinv cg gs2.G.graph.T.sorts gs2.G.demands ({ gs = gs2; scopes = DS.empty_scopes; memo = I.Empty }))
  = let ds = { gs = gs2; scopes = DS.empty_scopes; memo = I.Empty } in
    T.lemma_table_grows_refl gs2.G.graph.T.sorts;
    lemma_view cg gs2.G.graph.T.sorts;
    DS.lemma_empty_scopes (CG.sort_count (view cg ds));
    DS.lemma_memo_empty (view cg ds) DS.empty_scopes

let lemma_dag_guard (budget:G.resource_budget) (cg:CG.cgraph) (c:binder_certificate) (cache:I.index_tree judgment)
                    (handles:list nat)
  : Lemma (requires CG.graph_inv cg /\ handles_ok cg c.binder_entries handles /\
                    cache_classified cache 0 c.binder_entries /\ DagChecked? (dag_guard budget cg c cache handles))
          (ensures (let t = GP.checked_demands (DagChecked?.state (dag_guard budget cg c cache handles)).gs in
                    0 <= c.binder_root /\ c.binder_root < L.length c.binder_entries /\
                    L.memP [] (scope_demanded t c.binder_root) /\
                    BS.entries_scoped t cache 0 c.binder_entries))
  = let gs0 = initial budget cg in
    lemma_initial budget cg;
    GP.lemma_backward_from gs0 c;
    let G.Go _ gs1 = G.backward_from gs0 c in
    GP.lemma_root_at_empty gs1 c.binder_root;
    let G.Go () gs2 = G.root_at_empty gs1 c.binder_root in
    let td = gs2.G.demands in
    let t1 = gs2.G.graph.T.sorts in
    lemma_start cg gs2;
    let ds0 = { gs = gs2; scopes = DS.empty_scopes; memo = I.Empty } in
    lemma_entries_checked cg t1 td ds0 cache 0 c.binder_entries handles;
    let DGo ds = entries_checked cg ds0 cache 0 c.binder_entries handles in
    let tf = ds.gs.G.graph.T.sorts in
    GP.lemma_same_demands t1 tf td;
    GP.lemma_entries_ext (GP.interp_demands tf td) (GP.interp_demands t1 td) cache 0 c.binder_entries;
    GP.lemma_demanded tf td c.binder_root;
    GP.lemma_mem_map (GP.interp_scope tf) [] (G.id_demanded td c.binder_root);
    FStar.List.Tot.Properties.mem_memP ([] <: list sort) (scope_demanded (GP.interp_demands tf td) c.binder_root)
