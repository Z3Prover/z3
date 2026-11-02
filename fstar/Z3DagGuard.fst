(*
   Z3DagGuard.fst

   The scope guard of binder certificates in the opt-in accounting mode
   `verified-dag-v1`: the algorithm of `Z3UnifiedProof.binder_scoped` (scopes
   demanded backwards from the root at `[]`, premises earlier entries, an
   introduction's premises at its binder sorts reversed in front of the
   user's scope; then every demanded scope of every entry checked forwards,
   premises included), on the checked expression graph built while the
   document was marshaled (`Z3CheckedGraph`):

   * the backward pass is `Z3CheckedGuard.backward_from`, with sort ids in
     the graph's sort table, so a scope is a list of checked sort ids;
   * an entry's judgment is the node of its formula, or that node's two
     children for an equation (`judgment_nodes`); a certificate is checked
     with one node per entry formula (`handles`), which the marshaler earned
     (`Z3CheckedGraph`, `Z3DagDocument`), never a native id;
   * each demanded scope is interned to a canonical scope id and the
     judgment's nodes are walked there with the memo of `Z3DagScope`, shared
     by all entries of the certificate: a node already recorded at that scope
     id is not walked again, a node used at another scope is.

   Units: those of `Z3CheckedGuard` for the backward pass, the binder sorts
   and the premise checks, those of `Z3DagScope` for scope ids and walks, and
   `1 + table_units` (validation) per entry and per judgment-node lookup.
   Nothing is kept across certificates: the memo and scope ids live in one
   run, and a refused or exhausted run yields no success.

   `Z3DagGuardProof.lemma_dag_guard`: a `DagChecked` result establishes
   `Z3BinderScope.entries_scoped` and the root at `[]`, as
   `Z3CheckedGuardProof.lemma_verified_guard` does for `verified-sorts-v1`.
*)
module Z3DagGuard

open Z3AstTheory
open Z3UnifiedProof
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module T = Z3CheckedTerms
module W = Z3CheckedScope
module G = Z3CheckedGuard
module CG = Z3CheckedGraph
module DS = Z3DagScope

noeq
type dstate = {
  gs: G.gstate;
  scopes: DS.scope_table;
  memo: DS.memo;
}

(* The marshaled graph, read with the guard's sort table. *)
let view (cg:CG.cgraph) (ds:dstate) : CG.cgraph = CG.with_sorts cg ds.gs.G.graph.T.sorts 0 0

(* The nodes of a judgment of the entry whose formula is node `h`. *)
let judgment_nodes (cg:CG.cgraph) (h:nat) (j:judgment) : option (list nat) =
  match j with
  | Holds _ -> Some [h]
  | Equal _ _ | Observational _ _ ->
    (match CG.node_of cg h with
     | Some (T.ENApp _ [a; b] _) -> Some [a; b]
     | _ -> None)

noeq
type dstep =
  | DGo : st:dstate -> dstep
  | DStop : reason:G.failure -> dstep

(* Demanded scope `s` of entry `k`: the judgment's nodes walked at its id,
   then the premises demanded at the premise scope. *)
let scope_checked (cg:CG.cgraph) (ds:dstate) (k:int) (bids:option (list nat)) (ps:list int) (xs:list nat)
                  (s:list nat) : dstep =
  match W.count_within ds.gs.G.valid 0 s with
  | None -> DStop (G.Exhaust T.Validation)
  | Some (len, v) ->
    (match DS.intern_scope ds.scopes s v ds.gs.G.store with
     | DS.PushExhausted p -> DStop (G.Exhaust p)
     | DS.Pushed sc sid v1 s1 ->
       (match DS.walk (view cg ds) sc ds.memo v1 s1 (DS.visits xs sid []) with
        | DS.WalkExhausted p -> DStop (G.Exhaust p)
        | DS.WalkFailed -> DStop G.Refuse
        | DS.Walked sc' m' v2 s2 ->
          (match DS.all_recorded m' xs sid v2 with
           | None -> DStop (G.Exhaust T.Validation)
           | Some (false, _) -> DStop G.Refuse
           | Some (true, v3) ->
             let gs1 = { ds.gs with G.valid = v3; G.store = s2 } in
             (match G.premise_scope gs1 bids s len with
              | G.Stop f -> DStop f
              | G.Go (s', _) gs2 ->
                (match G.premises_checked gs2 k ps s' with
                 | G.Stop f -> DStop f
                 | G.Go () gs3 -> DGo ({ gs = gs3; scopes = sc'; memo = m' }))))))

let rec entry_checked (cg:CG.cgraph) (ds:dstate) (k:int) (bids:option (list nat)) (ps:list int) (xs:list nat)
                      (scopes:list (list nat))
  : Tot dstep (decreases scopes) =
  match scopes with
  | [] -> DGo ds
  | s :: rest ->
    (match scope_checked cg ds k bids ps xs s with
     | DGo ds' -> entry_checked cg ds' k bids ps xs rest
     | DStop f -> DStop f)

(* Entry `k`, with formula node `h`, demanded at `scopes`. *)
let entry_step (cg:CG.cgraph) (ds:dstate) (k:nat) (e:binder_entry) (j:judgment) (h:nat)
               (scopes:list (list nat)) : dstep =
  match G.spend_valid ds.gs (1 + CS.table_units) with
  | None -> DStop (G.Exhaust T.Validation)
  | Some gs0 ->
    if h >= CG.node_count cg then DStop G.Refuse
    else
      match judgment_nodes cg h j with
      | None -> DStop G.Refuse
      | Some xs ->
        (match G.entry_binders gs0 e with
         | G.Stop f -> DStop f
         | G.Go bids gs1 -> entry_checked cg ({ ds with gs = gs1 }) k bids e.binder_premises xs scopes)

let rec entries_checked (cg:CG.cgraph) (ds:dstate) (cache:I.index_tree judgment) (k:nat)
                        (entries:list binder_entry) (handles:list nat)
  : Tot dstep (decreases entries) =
  match entries, handles with
  | [], [] -> DGo ds
  | e :: rest, h :: hs ->
    (match G.spend_valid ds.gs (1 + CS.table_units) with
     | None -> DStop (G.Exhaust T.Validation)
     | Some gs0 ->
       let ds0 = { ds with gs = gs0 } in
       (match I.index_find cache k with
        | None -> DStop G.Refuse
        | Some j ->
          (match G.id_demanded gs0.G.demands k with
           | [] -> entries_checked cg ds0 cache (k + 1) rest hs
           | scopes ->
             (match entry_step cg ds0 k e j h scopes with
              | DGo ds1 -> entries_checked cg ds1 cache (k + 1) rest hs
              | DStop f -> DStop f))))
  | _, _ -> DStop G.Refuse

noeq
type dag_result =
  | DagChecked : state:dstate -> dag_result
  | DagRefused
  | DagExhausted : phase:T.phase -> dag_result

let initial (budget:G.resource_budget) (cg:CG.cgraph) : G.gstate =
  { G.graph = { T.empty_graph with T.sorts = cg.CG.terms.T.sorts }; G.demands = I.Empty;
    G.prep = budget.G.preparation; G.valid = budget.G.validation; G.store = budget.G.storage }

let dag_guard (budget:G.resource_budget) (cg:CG.cgraph) (c:binder_certificate) (cache:I.index_tree judgment)
              (handles:list nat) : dag_result =
  match G.backward_from (initial budget cg) c with
  | G.Stop G.Refuse -> DagRefused
  | G.Stop (G.Exhaust p) -> DagExhausted p
  | G.Go _ gs1 ->
    (match G.root_at_empty gs1 c.binder_root with
     | G.Stop G.Refuse -> DagRefused
     | G.Stop (G.Exhaust p) -> DagExhausted p
     | G.Go () gs2 ->
       (match entries_checked cg ({ gs = gs2; scopes = DS.empty_scopes; memo = I.Empty }) cache 0
                c.binder_entries handles with
        | DGo ds -> DagChecked ds
        | DStop G.Refuse -> DagRefused
        | DStop (G.Exhaust p) -> DagExhausted p))
