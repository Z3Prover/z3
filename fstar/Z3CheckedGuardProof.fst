(*
   Z3CheckedGuardProof.fst

   What the guard of the versioned mode (`Z3CheckedGuard.verified_guard`)
   establishes, with no semantic model and no assumption on its inputs.

   * `lemma_verified_guard`: a `Checked` run on a certificate and a cache
     establishes, for the demand table its scope ids denote
     (`checked_demands`), that the root is an entry, that it is assigned `[]`,
     and `Z3BinderScope.entries_scoped`: every demanded scope of every entry
     scopes its judgment, and every premise is an earlier entry assigned the
     premise scope. These are the facts `Z3BinderScope.lemma_guard` derives
     from the old guard's success; the theorems below follow from them as
     the old ones do.
   * Theorem 1, `lemma_verified_root_scoped`; theorem 2,
     `lemma_verified_edge_scoped`; for the checker,
     `lemma_verified_checked_guard` and `lemma_check_node_verified`: the
     opt-in node check accepts a quantifier introduction exactly when the
     default check accepts its shape, `check_binder_entries` builds a cache
     holding the conclusion at the root, and the verified guard holds on that
     cache; all other nodes are checked as by default.
*)
module Z3CheckedGuardProof

open Z3AstTheory
open Z3UnifiedProof
open Z3CheckedGuard
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module T = Z3CheckedTerms
module W = Z3CheckedScope
module D = Z3Definitions
module BS = Z3BinderScope
module SK = Z3Skolemization

(* --- The demand table the ids denote ------------------------------------------------------- *)

noextract
let rec tree_map (#a #b:Type) (f:a -> b) (t:I.index_tree a) : Tot (I.index_tree b) (decreases t) =
  match t with
  | I.Empty -> I.Empty
  | I.Branch v l r -> I.Branch (match v with Some x -> Some (f x) | None -> None) (tree_map f l) (tree_map f r)

let rec lemma_tree_map (#a #b:Type) (f:a -> b) (t:I.index_tree a) (k:nat)
  : Lemma (ensures I.index_get (tree_map f t) k == (match I.index_get t k with Some x -> Some (f x) | None -> None))
          (decreases k)
  = match t with
    | I.Empty -> ()
    | I.Branch _ l r ->
      if k = 0 then ()
      else if k % 2 = 1 then lemma_tree_map f l ((k - 1) / 2)
      else lemma_tree_map f r ((k - 1) / 2)

noextract
let interp_scope (t:CS.sort_table) (s:list nat) : list sort = L.map (T.interp t) s

noextract
let interp_scopes (t:CS.sort_table) (ss:list (list nat)) : list (list sort) = L.map (interp_scope t) ss

noextract
let interp_demands (t:CS.sort_table) (td:id_demands) : scope_demands = tree_map (interp_scopes t) td

let lemma_demanded (t:CS.sort_table) (td:id_demands) (k:int)
  : Lemma (scope_demanded (interp_demands t td) k == interp_scopes t (id_demanded td k))
  = if k >= 0 then lemma_tree_map (interp_scopes t) td k

(* The demand table of a checked run. *)
noextract
let checked_demands (st:gstate) : scope_demands = interp_demands st.graph.T.sorts st.demands

(* --- Valid ids ---------------------------------------------------------------------------------- *)

noextract
let rec scopes_below (ss:list (list nat)) (n:nat) : Tot bool (decreases ss) =
  match ss with
  | [] -> true
  | s :: rest -> CS.all_below s n && scopes_below rest n

let demands_ok (td:id_demands) (n:nat) : prop = forall (k:int). scopes_below (id_demanded td k) n

let rec lemma_scopes_widen (ss:list (list nat)) (n n':nat)
  : Lemma (requires scopes_below ss n /\ n <= n') (ensures scopes_below ss n') (decreases ss)
  = match ss with
    | [] -> ()
    | s :: rest -> T.lemma_all_below_widen s n n'; lemma_scopes_widen rest n n'

let lemma_demands_widen (td:id_demands) (n n':nat)
  : Lemma (requires demands_ok td n /\ n <= n') (ensures demands_ok td n')
  = let aux (k:int) : Lemma (scopes_below (id_demanded td k) n') = lemma_scopes_widen (id_demanded td k) n n' in
    FStar.Classical.forall_intro aux

let lemma_demands_put (td:id_demands) (n:nat) (k:nat) (v:list (list nat))
  : Lemma (requires demands_ok td n /\ scopes_below v n) (ensures demands_ok (I.index_put td k v) n)
  = let aux (q:int) : Lemma (scopes_below (id_demanded (I.index_put td k v) q) n)
      = if q >= 0 then I.lemma_index_put td k v q in
    FStar.Classical.forall_intro aux

let rec lemma_mem_below (s:list nat) (ss:list (list nat)) (n:nat)
  : Lemma (requires L.mem s ss /\ scopes_below ss n) (ensures CS.all_below s n) (decreases ss)
  = match ss with
    | x :: rest -> if x = s then () else lemma_mem_below s rest n

let rec lemma_scopes_agree (t t':CS.sort_table) (ss:list (list nat))
  : Lemma (requires T.table_grows t t' /\ scopes_below ss t.CS.node_count)
          (ensures interp_scopes t' ss == interp_scopes t ss) (decreases ss)
  = match ss with
    | [] -> ()
    | s :: rest -> CS.lemma_map_agree t t' t.CS.node_count s; lemma_scopes_agree t t' rest

let lemma_demanded_agree (t t':CS.sort_table) (td:id_demands) (k:int)
  : Lemma (requires T.table_grows t t' /\ demands_ok td t.CS.node_count)
          (ensures scope_demanded (interp_demands t' td) k == scope_demanded (interp_demands t td) k)
  = lemma_demanded t td k;
    lemma_demanded t' td k;
    lemma_scopes_agree t t' (id_demanded td k)

(* --- Primitive results ---------------------------------------------------------------------------- *)

let rec lemma_ids_eq (work:nat) (a b:list nat)
  : Lemma (ensures (match ids_eq work a b with Some (r, _) -> r == (a = b) | None -> True)) (decreases a)
  = if work = 0 then ()
    else match a, b with
         | x :: a', y :: b' -> if x = y then lemma_ids_eq (work - 1) a' b'
         | _, _ -> ()

let rec lemma_scope_mem (work:nat) (s:list nat) (ss:list (list nat))
  : Lemma (ensures (match scope_mem work s ss with Some (r, _) -> r == L.mem s ss | None -> True)) (decreases ss)
  = match ss with
    | [] -> ()
    | x :: rest ->
      lemma_ids_eq work x s;
      (match ids_eq work x s with
       | Some (false, w) -> lemma_scope_mem w s rest
       | _ -> ())

let rec lemma_mem_map (#a #b:eqtype) (f:a -> b) (x:a) (l:list a)
  : Lemma (requires L.mem x l) (ensures L.mem (f x) (L.map f l)) (decreases l)
  = match l with
    | y :: rest -> if y = x then () else lemma_mem_map f x rest

(* --- Invariants ------------------------------------------------------------------------------------- *)

let inv (st:gstate) : prop = T.graph_ok st.graph /\ demands_ok st.demands st.graph.T.sorts.CS.node_count

let grows (st st':gstate) : prop = T.graph_grows st.graph st'.graph

let lemma_grows_trans (a b c:gstate) : Lemma (requires grows a b /\ grows b c) (ensures grows a c)
  = T.lemma_graph_grows_trans a.graph b.graph c.graph

let step_ok (#a:Type) (st:gstate) (r:step a) (post:a -> gstate -> prop) : prop =
  match r with
  | Go v st' -> inv st' /\ grows st st' /\ post v st'
  | Stop _ -> True

let lemma_entry_binders (st:gstate) (e:binder_entry)
  : Lemma (requires inv st)
          (ensures step_ok st (entry_binders st e) (fun bids st' ->
                     st'.demands == st.demands /\
                     (match bids, e.binder_sorts with
                      | None, None -> True
                      | Some ids, Some bs ->
                        CS.all_below ids st'.graph.T.sorts.CS.node_count /\ L.map (T.interp st'.graph.T.sorts) ids == bs
                      | _, _ -> False)))
  = match e.binder_sorts with
    | None -> T.lemma_graph_grows_refl st.graph
    | Some bs ->
      T.lemma_intern_sorts st.graph.T.sorts bs st.prep st.store;
      (match T.intern_sorts st.graph.T.sorts bs st.prep st.store with
       | T.SortsInterned t _ _ _ _ -> lemma_demands_widen st.demands st.graph.T.sorts.CS.node_count t.CS.node_count
       | _ -> ())

(* The premise scope denotes `premise_scope_of` of the scope. *)
let premise_ids_ok (t:CS.sort_table) (e:binder_entry) (bids:option (list nat)) : prop =
  match bids, e.binder_sorts with
  | None, None -> True
  | Some ids, Some bs -> CS.all_below ids t.CS.node_count /\ L.map (T.interp t) ids == bs
  | _, _ -> False

let lemma_premise_scope (st:gstate) (e:binder_entry) (bids:option (list nat)) (s:list nat) (len:nat)
  : Lemma (requires inv st /\ premise_ids_ok st.graph.T.sorts e bids /\ CS.all_below s st.graph.T.sorts.CS.node_count)
          (ensures step_ok st (premise_scope st bids s len) (fun (r:list nat & nat) st' ->
                     st'.graph == st.graph /\ st'.demands == st.demands /\
                     CS.all_below (fst r) st.graph.T.sorts.CS.node_count /\
                     interp_scope st.graph.T.sorts (fst r) == BS.premise_scope_of e (interp_scope st.graph.T.sorts s)))
  = T.lemma_graph_grows_refl st.graph;
    match bids, e.binder_sorts with
    | Some ids, Some bs -> W.lemma_scope_under st.graph.T.sorts ids s
    | _, _ -> ()

(* --- The backward pass keeps valid ids --------------------------------------------------------------- *)

let lemma_demand (st:gstate) (k:nat) (scope:list nat) (count:nat)
  : Lemma (requires inv st /\ CS.all_below scope st.graph.T.sorts.CS.node_count)
          (ensures step_ok st (demand st k scope count) (fun _ _ -> True))
  = T.lemma_graph_grows_refl st.graph;
    match spend_valid st (1 + CS.table_units) with
    | None -> ()
    | Some st0 ->
      let old = id_demanded st0.demands k in
      (match scope_mem st0.valid scope old with
       | Some (false, v) ->
         (match W.count_within v 0 old with
          | Some (m, v') ->
            lemma_demands_put st0.demands st0.graph.T.sorts.CS.node_count k (scope :: old)
          | None -> ())
       | _ -> ())

let rec lemma_demand_premises (st:gstate) (k:int) (ps:list int) (scope:list nat) (count:nat)
  : Lemma (requires inv st /\ CS.all_below scope st.graph.T.sorts.CS.node_count)
          (ensures step_ok st (demand_premises st k ps scope count) (fun _ st' -> st'.graph == st.graph))
          (decreases ps)
  = T.lemma_graph_grows_refl st.graph;
    match ps with
    | [] -> ()
    | p :: rest ->
      if 0 <= p && p < k then begin
        lemma_demand st p scope count;
        match demand st p scope count with
        | Go c st' -> lemma_demand_premises st' k rest scope c
        | _ -> ()
      end

let rec lemma_demand_entry (st:gstate) (k:int) (e:binder_entry) (bids:option (list nat))
                           (scopes:list (list nat)) (count:nat)
  : Lemma (requires inv st /\ premise_ids_ok st.graph.T.sorts e bids /\
                    scopes_below scopes st.graph.T.sorts.CS.node_count)
          (ensures step_ok st (demand_entry st k bids e.binder_premises scopes count) (fun _ st' -> st'.graph == st.graph))
          (decreases scopes)
  = T.lemma_graph_grows_refl st.graph;
    match scopes with
    | [] -> ()
    | s :: rest ->
      (match W.count_within st.valid 0 s with
       | None -> ()
       | Some (len, v) ->
         let st' = { st with valid = v } in
         lemma_premise_scope st' e bids s len;
         (match premise_scope st' bids s len with
          | Go (s', _) st1 ->
            lemma_demand_premises st1 k e.binder_premises s' count;
            (match demand_premises st1 k e.binder_premises s' count with
             | Go c st2 -> lemma_demand_entry st2 k e bids rest c
             | _ -> ())
          | _ -> ()))

let rec lemma_demand_entries (st:gstate) (k:int) (reversed:list binder_entry) (count:nat)
  : Lemma (requires inv st)
          (ensures step_ok st (demand_entries st k reversed count) (fun _ _ -> True))
          (decreases reversed)
  = T.lemma_graph_grows_refl st.graph;
    match reversed with
    | [] -> ()
    | e :: rest ->
      (match spend_valid st (1 + CS.table_units) with
       | None -> ()
       | Some st0 ->
         (match id_demanded st0.demands k with
          | [] -> lemma_demand_entries st0 (k - 1) rest count
          | scopes ->
            lemma_entry_binders st0 e;
            (match entry_binders st0 e with
             | Go bids st1 ->
               lemma_scopes_widen scopes st0.graph.T.sorts.CS.node_count st1.graph.T.sorts.CS.node_count;
               lemma_demand_entry st1 k e bids scopes count;
               (match demand_entry st1 k bids e.binder_premises scopes count with
                | Go c st2 ->
                  lemma_demand_entries st2 (k - 1) rest c;
                  (match demand_entries st2 (k - 1) rest c with
                   | Go _ st3 -> lemma_grows_trans st0 st1 st2; lemma_grows_trans st0 st2 st3
                   | _ -> ())
                | _ -> ())
             | _ -> ())))

(* --- The forward pass establishes the specification ------------------------------------------- *)

let lemma_judgment_scoped (sc:list sort) (j:judgment)
  : Lemma (requires D.scoped_args sc (judgment_exprs j) == true) (ensures BS.binder_judgment_scoped sc j)
  = ()

let rec lemma_represents_snoc (g:T.term_graph) (xs:list nat) (es:list expr) (x:nat) (e:expr)
  : Lemma (requires T.represents_list g xs es /\ T.represents g x e)
          (ensures T.represents_list g (L.append xs [x]) (L.append es [e])) (decreases es)
  = match xs, es with
    | _ :: xs', _ :: es' -> lemma_represents_snoc g xs' es' x e
    | _, _ -> ()

let rec lemma_prepare_list (st:gstate) (es:list expr) (acc:list nat) (done:list expr)
  : Lemma (requires inv st /\ T.represents_list st.graph (L.rev acc) done)
          (ensures step_ok st (prepare_list st es acc) (fun xs st' ->
                     st'.demands == st.demands /\ T.represents_list st'.graph xs (L.append done es)))
          (decreases es)
  = T.lemma_graph_grows_refl st.graph;
    match es with
    | [] -> L.append_l_nil done
    | e :: rest ->
      if st.store < 2 then ()
      else begin
        T.lemma_prepare_expr st.graph e st.prep (st.store - 2);
        match T.prepare_expr st.graph e st.prep (st.store - 2) with
        | T.Prepared g x _ w s ->
          let st' = { st with graph = g; prep = w; store = s } in
          lemma_demands_widen st.demands st.graph.T.sorts.CS.node_count g.T.sorts.CS.node_count;
          T.lemma_represents_list_grows st.graph g (L.rev acc) done;
          lemma_represents_snoc g (L.rev acc) done x e;
          Z3List.lemma_rev_cons x acc;
          L.append_assoc done [e] rest;
          lemma_prepare_list st' rest (x :: acc) (L.append done [e]);
          (match prepare_list st' rest (x :: acc) with
           | Go _ st'' -> lemma_grows_trans st st' st''
           | _ -> ())
        | _ -> ()
      end

(* The demand table after the backward pass is `td`, valid in `t1`; later
   graphs extend `t1`. *)
let fwd (t1:CS.sort_table) (td:id_demands) (st:gstate) : prop =
  inv st /\ st.demands == td /\ T.table_grows t1 st.graph.T.sorts /\ demands_ok td t1.CS.node_count

let rec lemma_premises_checked (t1:CS.sort_table) (td:id_demands) (st:gstate) (k:int) (ps:list int) (s':list nat)
  : Lemma (requires fwd t1 td st /\ Go? (premises_checked st k ps s'))
          (ensures (let Go _ st' = premises_checked st k ps s' in
                    st'.graph == st.graph /\ st'.demands == st.demands /\
                    BS.premises_demanded (interp_demands t1 td) k ps (interp_scope st.graph.T.sorts s')))
          (decreases ps)
  = match ps with
    | [] -> ()
    | p :: rest ->
      let st0 = Some?.v (spend_valid st (1 + CS.table_units)) in
      lemma_scope_mem st0.valid s' (id_demanded td p);
      let v = snd (Some?.v (scope_mem st0.valid s' (id_demanded td p))) in
      lemma_premises_checked t1 td ({ st0 with valid = v }) k rest s';
      lemma_mem_below s' (id_demanded td p) t1.CS.node_count;
      CS.lemma_map_agree t1 st.graph.T.sorts t1.CS.node_count s';
      lemma_mem_map (interp_scope t1) s' (id_demanded td p);
      lemma_demanded t1 td p

let lemma_walk_scoped (st:gstate) (j:judgment) (s:list nat) (len:nat) (xs:list nat) (v:nat)
  : Lemma (requires inv st /\ len == L.length s /\ CS.all_below s st.graph.T.sorts.CS.node_count /\
                    T.represents_list st.graph xs (judgment_exprs j) /\
                    W.walk_true (W.check_scoped st.graph s len xs v st.store))
          (ensures BS.binder_judgment_scoped (interp_scope st.graph.T.sorts s) j)
  = W.lemma_check_scoped st.graph s len xs v st.store (judgment_exprs j);
    lemma_judgment_scoped (interp_scope st.graph.T.sorts s) j

(* One demanded scope `s` of entry `k`, checked: the judgment is scoped at it
   and the premises are demanded at the premise scope. *)
let lemma_scope_checked (t1:CS.sort_table) (td:id_demands) (st:gstate) (k:int) (e:binder_entry)
                        (bids:option (list nat)) (xs:list nat) (j:judgment) (s:list nat) (len v:nat)
  : Lemma (requires fwd t1 td st /\ premise_ids_ok st.graph.T.sorts e bids /\
                    T.represents_list st.graph xs (judgment_exprs j) /\ CS.all_below s t1.CS.node_count /\
                    len == L.length s /\ W.walk_true (W.check_scoped st.graph s len xs v st.store))
          (ensures (let W.Walked _ v1 s1 = W.check_scoped st.graph s len xs v st.store in
                    let st' = { st with valid = v1; store = s1 } in
                    match premise_scope st' bids s len with
                    | Go (s', _) st1 ->
                      fwd t1 td st1 /\ st1.graph == st.graph /\
                      (Go? (premises_checked st1 k e.binder_premises s') ==>
                       (let Go _ st2 = premises_checked st1 k e.binder_premises s' in
                        fwd t1 td st2 /\ st2.graph == st.graph /\
                        BS.binder_judgment_scoped (interp_scope t1 s) j /\
                        BS.premises_demanded (interp_demands t1 td) k e.binder_premises
                          (BS.premise_scope_of e (interp_scope t1 s))))
                    | Stop _ -> True))
  = let g = st.graph in
    T.lemma_all_below_widen s t1.CS.node_count g.T.sorts.CS.node_count;
    lemma_walk_scoped st j s len xs v;
    CS.lemma_map_agree t1 g.T.sorts t1.CS.node_count s;
    let W.Walked _ v1 s1 = W.check_scoped g s len xs v st.store in
    let st' = { st with valid = v1; store = s1 } in
    lemma_premise_scope st' e bids s len;
    match premise_scope st' bids s len with
    | Go (s', _) st1 ->
      if Go? (premises_checked st1 k e.binder_premises s')
      then lemma_premises_checked t1 td st1 k e.binder_premises s'
    | Stop _ -> ()

let rec lemma_entry_checked (t1:CS.sort_table) (td:id_demands) (st:gstate) (k:int) (e:binder_entry)
                            (bids:option (list nat)) (xs:list nat) (j:judgment) (scopes:list (list nat))
  : Lemma (requires fwd t1 td st /\ premise_ids_ok st.graph.T.sorts e bids /\
                    T.represents_list st.graph xs (judgment_exprs j) /\ scopes_below scopes t1.CS.node_count /\
                    Go? (entry_checked st k bids e.binder_premises xs scopes))
          (ensures (let Go _ st' = entry_checked st k bids e.binder_premises xs scopes in
                    fwd t1 td st' /\ st'.graph == st.graph /\
                    BS.entry_scoped (interp_demands t1 td) k e j (interp_scopes t1 scopes)))
          (decreases scopes)
  = match scopes with
    | [] -> ()
    | s :: rest ->
      W.lemma_count_within st.valid 0 s;
      let len, v = Some?.v (W.count_within st.valid 0 s) in
      let st0 = { st with valid = v } in
      lemma_scope_checked t1 td st0 k e bids xs j s len v;
      let W.Walked _ v1 s1 = W.check_scoped st0.graph s len xs v st0.store in
      let st' = { st0 with valid = v1; store = s1 } in
      let Go (s', _) st1 = premise_scope st' bids s len in
      let Go _ st2 = premises_checked st1 k e.binder_premises s' in
      lemma_entry_checked t1 td st2 k e bids xs j rest

let lemma_fwd_grows (t1:CS.sort_table) (td:id_demands) (st st':gstate)
  : Lemma (requires fwd t1 td st /\ inv st' /\ grows st st' /\ st'.demands == td) (ensures fwd t1 td st')
  = T.lemma_table_grows_trans t1 st.graph.T.sorts st'.graph.T.sorts

(* One entry's preparation: its judgment's nodes and binder ids. *)
let lemma_entry_prepared (t1:CS.sort_table) (td:id_demands) (st0:gstate) (e:binder_entry) (j:judgment)
  : Lemma (requires fwd t1 td st0)
          (ensures (match prepare_list st0 (judgment_exprs j) [] with
                    | Go xs st1 ->
                      fwd t1 td st1 /\ grows st0 st1 /\
                      (match entry_binders st1 e with
                       | Go bids st2 ->
                         fwd t1 td st2 /\ grows st0 st2 /\ premise_ids_ok st2.graph.T.sorts e bids /\
                         T.represents_list st2.graph xs (judgment_exprs j)
                       | Stop _ -> True)
                    | Stop _ -> True))
  = lemma_prepare_list st0 (judgment_exprs j) [] [];
    match prepare_list st0 (judgment_exprs j) [] with
    | Go xs st1 ->
      lemma_fwd_grows t1 td st0 st1;
      lemma_entry_binders st1 e;
      (match entry_binders st1 e with
       | Go bids st2 ->
         lemma_fwd_grows t1 td st1 st2;
         lemma_grows_trans st0 st1 st2;
         T.lemma_represents_list_grows st1.graph st2.graph xs (judgment_exprs j)
       | Stop _ -> ())
    | Stop _ -> ()

let lemma_entry_step (t1:CS.sort_table) (td:id_demands) (st0:gstate) (k:nat) (e:binder_entry) (j:judgment)
                     (scopes:list (list nat))
  : Lemma (requires fwd t1 td st0 /\ scopes_below scopes t1.CS.node_count /\ Go? (entry_step st0 k e j scopes))
          (ensures (let Go _ st3 = entry_step st0 k e j scopes in
                    fwd t1 td st3 /\ grows st0 st3 /\
                    BS.entry_scoped (interp_demands t1 td) k e j (interp_scopes t1 scopes)))
  = lemma_entry_prepared t1 td st0 e j;
    let Go xs st1 = prepare_list st0 (judgment_exprs j) [] in
    let Go bids st2 = entry_binders st1 e in
    lemma_entry_checked t1 td st2 k e bids xs j scopes

let rec lemma_entries_checked (t1:CS.sort_table) (td:id_demands) (st:gstate) (cache:I.index_tree judgment)
                              (k:nat) (entries:list binder_entry)
  : Lemma (requires fwd t1 td st /\ Go? (entries_checked st cache k entries))
          (ensures (let Go _ st' = entries_checked st cache k entries in
                    fwd t1 td st' /\ grows st st' /\
                    BS.entries_scoped (interp_demands t1 td) cache k entries))
          (decreases entries)
  = T.lemma_graph_grows_refl st.graph;
    match entries with
    | [] -> ()
    | e :: rest ->
      let st0 = Some?.v (spend_valid st (1 + CS.table_units)) in
      let j = Some?.v (I.index_find cache k) in
      lemma_demanded t1 td k;
      (match id_demanded td k with
       | [] ->
         lemma_entries_checked t1 td st0 cache (k + 1) rest
       | scopes ->
         lemma_entry_step t1 td st0 k e j scopes;
         let Go _ st3 = entry_step st0 k e j scopes in
         lemma_entries_checked t1 td st3 cache (k + 1) rest;
         let Go _ st4 = entries_checked st3 cache (k + 1) rest in
         lemma_grows_trans st0 st3 st4)

(* --- Equal demanded scopes, equal specification ------------------------------------------------ *)

let same_demands (ta tb:scope_demands) : prop = forall (p:int). scope_demanded ta p == scope_demanded tb p

let rec lemma_premises_ext (ta tb:scope_demands) (k:int) (ps:list int) (scope:list sort)
  : Lemma (requires same_demands ta tb)
          (ensures BS.premises_demanded ta k ps scope == BS.premises_demanded tb k ps scope) (decreases ps)
  = match ps with [] -> () | p :: rest -> lemma_premises_ext ta tb k rest scope

let rec lemma_entry_ext (ta tb:scope_demands) (k:int) (e:binder_entry) (j:judgment) (scopes:list (list sort))
  : Lemma (requires same_demands ta tb)
          (ensures BS.entry_scoped ta k e j scopes == BS.entry_scoped tb k e j scopes) (decreases scopes)
  = match scopes with
    | [] -> ()
    | s :: rest ->
      lemma_premises_ext ta tb k e.binder_premises (BS.premise_scope_of e s);
      lemma_entry_ext ta tb k e j rest

let rec lemma_entries_ext (ta tb:scope_demands) (cache:I.index_tree judgment) (k:nat) (entries:list binder_entry)
  : Lemma (requires same_demands ta tb)
          (ensures BS.entries_scoped ta cache k entries == BS.entries_scoped tb cache k entries) (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      (match I.index_find cache k with
       | Some j -> lemma_entry_ext ta tb k e j (scope_demanded ta k)
       | None -> ());
      lemma_entries_ext ta tb cache (k + 1) rest

let lemma_same_demands (t t':CS.sort_table) (td:id_demands)
  : Lemma (requires T.table_grows t t' /\ demands_ok td t.CS.node_count)
          (ensures same_demands (interp_demands t' td) (interp_demands t td))
  = let aux (p:int) : Lemma (scope_demanded (interp_demands t' td) p == scope_demanded (interp_demands t td) p)
      = lemma_demanded_agree t t' td p in
    FStar.Classical.forall_intro aux

(* --- The guard ------------------------------------------------------------------------------------- *)

let lemma_empty_graph () : Lemma (T.graph_ok T.empty_graph)
  = CS.lemma_initial_state ({ CS.preparation = 0; CS.storage = 0 })

let lemma_demands_empty (n:nat) : Lemma (demands_ok I.Empty n) = ()

(* The backward pass: a valid state, and the root an entry. *)
let lemma_backward_start (budget:resource_budget) (root:int) (n v:nat)
  : Lemma (requires 0 <= root /\ root < n /\ (initial budget).store >= n + 2 + CS.table_units /\ v >= CS.table_units)
          (ensures inv ({ initial budget with demands = I.index_put I.Empty root [[]]; valid = v - CS.table_units;
                                             store = (initial budget).store - (n + 2 + CS.table_units) }))
  = lemma_empty_graph ();
    lemma_demands_empty 0;
    lemma_demands_put I.Empty 0 root [[]]

let lemma_backward (budget:resource_budget) (c:binder_certificate)
  : Lemma (match backward budget c with
           | Go n st1 -> inv st1 /\ n == L.length c.binder_entries /\ 0 <= c.binder_root /\ c.binder_root < n
           | Stop _ -> True)
  = let st = initial budget in
    W.lemma_count_within st.valid 0 c.binder_entries;
    match W.count_within st.valid 0 c.binder_entries with
    | Some (n, v) ->
      if 0 <= c.binder_root && c.binder_root < n && st.store >= n + 2 + CS.table_units && v >= CS.table_units then begin
        let st0 = { st with demands = I.index_put I.Empty c.binder_root [[]]; valid = v - CS.table_units;
                            store = st.store - (n + 2 + CS.table_units) } in
        lemma_backward_start budget c.binder_root n v;
        lemma_demand_entries st0 (n - 1) (L.rev c.binder_entries) (binder_demand_limit n)
      end
    | None -> ()

let lemma_root_at_empty (st:gstate) (root:int)
  : Lemma (requires inv st)
          (ensures (match root_at_empty st root with
                    | Go () st2 ->
                      inv st2 /\ st2.graph == st.graph /\ st2.demands == st.demands /\
                      L.mem [] (id_demanded st.demands root)
                    | Stop _ -> True))
  = match spend_valid st CS.table_units with
    | Some st2 -> lemma_scope_mem st2.valid [] (id_demanded st2.demands root)
    | None -> ()

(* The forward pass from the state after the backward pass and the root check. *)
let lemma_forward (st1 st2:gstate) (cache:I.index_tree judgment) (entries:list binder_entry) (root:int)
  : Lemma (requires inv st1 /\ inv st2 /\ st2.graph == st1.graph /\ st2.demands == st1.demands /\
                    L.mem [] (id_demanded st1.demands root) /\ Go? (entries_checked st2 cache 0 entries))
          (ensures (let Go _ st3 = entries_checked st2 cache 0 entries in
                    let t = checked_demands st3 in
                    L.memP [] (scope_demanded t root) /\ BS.entries_scoped t cache 0 entries))
  = let td = st1.demands in
    let t1 = st1.graph.T.sorts in
    T.lemma_table_grows_refl t1;
    lemma_entries_checked t1 td st2 cache 0 entries;
    let Go () st3 = entries_checked st2 cache 0 entries in
    let tf = st3.graph.T.sorts in
    lemma_same_demands t1 tf td;
    lemma_entries_ext (interp_demands tf td) (interp_demands t1 td) cache 0 entries;
    lemma_demanded tf td root;
    lemma_mem_map (interp_scope tf) [] (id_demanded td root);
    FStar.List.Tot.Properties.mem_memP ([] <: list sort) (scope_demanded (interp_demands tf td) root)

(* A `Checked` run establishes the specification the old guard's success
   establishes (`Z3BinderScope.lemma_guard`), for the demand table its ids
   denote. *)
let lemma_verified_guard (budget:resource_budget) (c:binder_certificate) (cache:I.index_tree judgment)
  : Lemma (requires Checked? (verified_guard budget c cache))
          (ensures (let t = checked_demands (Checked?.state (verified_guard budget c cache)) in
                    0 <= c.binder_root /\ c.binder_root < L.length c.binder_entries /\
                    L.memP [] (scope_demanded t c.binder_root) /\
                    BS.entries_scoped t cache 0 c.binder_entries))
  = lemma_backward budget c;
    let Go _ st1 = backward budget c in
    lemma_root_at_empty st1 c.binder_root;
    let Go () st2 = root_at_empty st1 c.binder_root in
    lemma_forward st1 st2 cache c.binder_entries c.binder_root

(* Theorem 1: the root is an entry, assigned `[]`, and scoped at `[]`. *)
let lemma_verified_root_scoped (budget:resource_budget) (c:binder_certificate) (cache:I.index_tree judgment)
  : Lemma (requires Checked? (verified_guard budget c cache))
          (ensures 0 <= c.binder_root /\ c.binder_root < L.length c.binder_entries /\
                   Some? (I.index_find cache c.binder_root) /\
                   BS.binder_judgment_scoped [] (Some?.v (I.index_find cache c.binder_root)))
  = lemma_verified_guard budget c cache;
    let t = checked_demands (Checked?.state (verified_guard budget c cache)) in
    let root : nat = c.binder_root in
    BS.lemma_scoped_at t cache c.binder_entries root []

(* Theorem 2: every edge used at a demanded scope is scoped under the user's binders. *)
let lemma_verified_edge_scoped (budget:resource_budget) (c:binder_certificate) (cache:I.index_tree judgment)
                               (k:nat) (s:list sort) (p:int)
  : Lemma (requires Checked? (verified_guard budget c cache) /\ k < L.length c.binder_entries /\
                    L.memP s (scope_demanded (checked_demands (Checked?.state (verified_guard budget c cache))) k) /\
                    L.memP p (L.index c.binder_entries k).binder_premises)
          (ensures (let t = checked_demands (Checked?.state (verified_guard budget c cache)) in
                    let s' = BS.premise_scope_of (L.index c.binder_entries k) s in
                    Some? (I.index_find cache k) /\ BS.binder_judgment_scoped s (Some?.v (I.index_find cache k)) /\
                    0 <= p /\ p < k /\ L.memP s' (scope_demanded t p) /\
                    Some? (I.index_find cache p) /\ BS.binder_judgment_scoped s' (Some?.v (I.index_find cache p))))
  = lemma_verified_guard budget c cache;
    let t = checked_demands (Checked?.state (verified_guard budget c cache)) in
    BS.lemma_scoped_at t cache c.binder_entries k s;
    let s' = BS.premise_scope_of (L.index c.binder_entries k) s in
    BS.lemma_premises_demanded t k (L.index c.binder_entries k).binder_premises s' p;
    BS.lemma_scoped_at t cache c.binder_entries p s'

(* --- The checker ------------------------------------------------------------------------------------ *)

let lemma_verified_checked_guard (skolems:list SK.definition) (assertions:list judgment)
                                 (c:binder_certificate) (concl:judgment)
  : Lemma (requires check_binder_verified skolems assertions c concl)
          (ensures Some? (check_binder_entries skolems assertions c.binder_entries I.Empty 0) /\
                   (let cache = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
                    let n = L.length c.binder_entries in
                    I.index_find cache c.binder_root == Some concl /\
                    Checked? (verified_guard (verified_budget n) c cache)))
  = BS.lemma_count_cells 0 c.binder_entries

let lemma_verified_checked_root_scoped (skolems:list SK.definition) (assertions:list judgment)
                                       (c:binder_certificate) (concl:judgment)
  : Lemma (requires check_binder_verified skolems assertions c concl)
          (ensures BS.binder_judgment_scoped [] concl)
  = lemma_verified_checked_guard skolems assertions c concl;
    let cache = Some?.v (check_binder_entries skolems assertions c.binder_entries I.Empty 0) in
    lemma_verified_root_scoped (verified_budget (L.length c.binder_entries)) c cache

(* The opt-in node check differs from the default only in the guard deciding
   a quantifier introduction's pending count. *)
let lemma_check_node_verified (skolems:list SK.definition) (strict:bool) (assertions:list judgment)
                              (contains:judgment -> bool) (node:proof_node)
  : Lemma (fst (check_node_verified skolems strict assertions contains node) ==
           (match check_node_with_membership skolems strict assertions contains node, node.kind with
            | Some (fact, _), QuantifierIntroduction c ->
              Some (fact, (if check_binder_verified skolems assertions c node.conclusion then 0 else 1))
            | r, _ -> r))
  = ()
