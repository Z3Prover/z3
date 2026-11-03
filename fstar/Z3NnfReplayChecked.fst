(*
   Z3NnfReplayChecked.fst

   The replay of an NNF or quantifier-introduction certificate
   (`Z3NnfReplay.replay`) with the scope guard of an opt-in accounting mode
   in place of the default guard.

   `Z3NnfReplay.replay` takes four scope facts from the default guard
   (`U.binder_scopes`, `U.scope_entries_checked`): the root is an entry
   demanded at `[]`, every demanded scope of every entry scopes its judgment,
   and every premise is an earlier entry demanded at the premise scope
   (`Z3BinderScope.entries_scoped`). `Z3NnfReplay.lemma_steps` derives the
   replay's truth induction from exactly those facts and the entries' local
   rules, over the demand table `t` only through `U.scope_demanded t k`.

   The checked guards earn the same facts for the demand table their scope
   ids denote (`Z3DagGuardProof.lemma_dag_guard`, `Z3CheckedGuardProof.
   lemma_verified_guard`). This module runs a checked guard on the cache
   that `Z3NnfReplay` itself builds (`judgments_of`: the classification of
   each entry's own formula, `lemma_judgments_classified`) and then the
   replay's own entry loop (`steps_ok_checked`) over the ids' demands, so
   that `Z3NnfReplay.lemma_steps` is reused unchanged:

   * `lemma_replay_dag` / `lemma_replay_sorts` state what
     `Z3NnfReplay.lemma_replay` states, for the same typed Root model: the
     conclusion is scoped at `[]` and holds in every model of the same
     universal and existential quantifier laws that makes the assertions
     true. No guard precondition of the default (its budget, its
     `check_binder_entries`) is used or required.
   * `DD.prepared` is the marshaler's earned form: its graph is invariant and
     its handles are nodes storing exactly the entries' formulas, by the type
     of the refined record, not by a flag a producer supplies.
   * The Skolem typing gate of the default loop (`Z3NnfReplay.
     skolem_scopes_ok`: an open dependent step is used only at scopes where
     its dependencies name positions of the scope with their sorts) is kept,
     not dropped: `skolem_gate` decides it on the scope ids, iteratively and
     charged, against the checked sort table (`sort_matches`: a sort value
     against a checked id by a worklist, `lemma_sort_matches`; reversed
     binders and array domains and ranges included), and is proved to agree
     with the default gate on the sorts the ids denote (`lemma_skolem_gate`).
     It reads no sort by the ghost interpretation `Z3CheckedSorts.interp_node`.
   * A selected opt-in route that cannot run (its certificate is not
     prepared) leaves the node pending, with the reason (`outcome`): there is
     no fallback to the default guard.

   Units of the Skolem gate, charged from the validation allowance the guard
   left: one per scope cell (the scope counted once per scope), one plus
   the scope's length per dependency, and for each task of `sort_matches`
   `1 + table_units` per sort node compared, one per child pair, and one plus
   the characters of a name compared (counted by the bounded counter, so a
   name longer than the allowance is exhaustion, not a long scan). A gate that
   exhausts its allowance leaves the node pending.
*)
module Z3NnfReplayChecked

open Z3AstTheory
module U = Z3UnifiedProof
module NR = Z3NnfReplay
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module CT = Z3CheckedTerms
module G = Z3CheckedGuard
module GP = Z3CheckedGuardProof
module W = Z3CheckedScope
module DG = Z3DagGuard
module DGP = Z3DagGuardProof
module CG = Z3CheckedGraph
module DD = Z3DagDocument
module DS = Z3DagScope
module BS = Z3BinderScope
module SK = Z3Skolemization
module SDS = Z3SortedDependentSkolem
module D = Z3Definitions
module S = Z3DatatypeSignature
module V = Z3DatatypeValue
module Q = Z3SortedQuantifier
module E = Z3SortedSkolem
module ST = Z3SortedSemantics

(* ---------------------------------------------------------------------- *)
(* 1. A sort value against a checked id                                     *)
(* ---------------------------------------------------------------------- *)

(* The work of `sort_matches`: a sort node of the table against a sort, or the
   remaining children of an array node against the remaining domain. *)
type match_task =
  | MPair : id:nat -> s:sort -> match_task
  | MKids : ids:list nat -> ss:list sort -> match_task

let match_cost : nat = 1 + CS.table_units

noextract
let task_holds (t:CS.sort_table) (k:match_task) : prop =
  match k with
  | MPair i s -> i < t.CS.node_count /\ CS.interp_node t i == s
  | MKids ids ss -> CS.all_below ids t.CS.node_count /\ L.map (CS.interp_node t) ids == ss

noextract
let rec tasks_hold (t:CS.sort_table) (ks:list match_task) : Tot prop (decreases ks) =
  match ks with
  | [] -> True
  | k :: rest -> task_holds t k /\ tasks_hold t rest

(* Whether every task holds: `Some (b, left)`, or `None` when `work` does not
   pay for the tasks. A worklist and a self tail call: no stack in the depth
   or the width of a sort. A name is compared only after the bounded counter
   has found it within the allowance. *)
let rec sort_matches (t:CS.sort_table) (work:nat) (tasks:list match_task)
  : Tot (option (bool & nat)) (decreases work) =
  match tasks with
  | [] -> Some (true, work)
  | MKids [] [] :: rest -> if work = 0 then None else sort_matches t (work - 1) rest
  | MKids (i :: ids) (s :: ss) :: rest ->
    if work = 0 then None else sort_matches t (work - 1) (MPair i s :: MKids ids ss :: rest)
  | MKids _ _ :: _ -> if work = 0 then None else Some (false, work - 1)
  | MPair i s :: rest ->
    if work < match_cost then None
    else
      let w = work - match_cost in
      if i >= t.CS.node_count then Some (false, w)
      else
        match CS.node_of t i, s with
        | Some (CS.NodeBase nm), BaseSort name ->
          (match CS.checked_name_units name w with
           | None -> None
           | Some len -> if nm = name then sort_matches t (w - len) rest else Some (false, w - len))
        | Some (CS.NodeArray ids r), ArraySort ds rs ->
          sort_matches t w (MKids ids ds :: MPair r rs :: rest)
        | _, _ -> Some (false, w)

(* A node of a checked table, read by the interpretation. *)
let lemma_node_base (t:CS.sort_table{CS.valid_table t}) (i:nat) (nm:string)
  : Lemma (requires i < t.CS.node_count /\ CS.node_of t i == Some (CS.NodeBase nm))
          (ensures CS.interp_node t i == BaseSort nm)
  = CS.lemma_interp_node t i

let lemma_node_array (t:CS.sort_table{CS.valid_table t}) (i:nat) (ids:list nat) (r:nat)
  : Lemma (requires i < t.CS.node_count /\ CS.node_of t i == Some (CS.NodeArray ids r))
          (ensures CS.all_below ids t.CS.node_count /\ r < t.CS.node_count /\
                   CS.interp_node t i == ArraySort (L.map (CS.interp_node t) ids) (CS.interp_node t r))
  = CS.lemma_interp_node t i;
    assert (Some? (CS.node_of t i) /\ CS.children_below (Some?.v (CS.node_of t i)) i);
    CT.lemma_all_below_widen ids i t.CS.node_count

(* `sort_matches` decides, exactly, whether the tasks hold of the sorts the
   table's ids denote. *)
let rec lemma_sort_matches (t:CS.sort_table{CS.valid_table t}) (work:nat) (tasks:list match_task)
  : Lemma (ensures (match sort_matches t work tasks with
                    | Some (true, _) -> tasks_hold t tasks
                    | Some (false, _) -> ~(tasks_hold t tasks)
                    | None -> True))
          (decreases work)
  = match tasks with
    | [] -> ()
    | MKids [] [] :: rest -> if work > 0 then lemma_sort_matches t (work - 1) rest
    | MKids (i :: ids) (s :: ss) :: rest ->
      if work > 0 then lemma_sort_matches t (work - 1) (MPair i s :: MKids ids ss :: rest)
    | MKids _ _ :: _ -> ()
    | MPair i s :: rest ->
      if work >= match_cost then begin
        let w = work - match_cost in
        if i < t.CS.node_count then begin
          CS.lemma_interp_node t i;
          match CS.node_of t i, s with
          | Some (CS.NodeBase nm), BaseSort name ->
            lemma_node_base t i nm;
            (match CS.checked_name_units name w with
             | None -> ()
             | Some len -> if nm = name then lemma_sort_matches t (w - len) rest)
          | Some (CS.NodeArray ids r), ArraySort ds rs ->
            lemma_node_array t i ids r;
            lemma_sort_matches t w (MKids ids ds :: MPair r rs :: rest)
          | Some (CS.NodeBase nm), ArraySort _ _ -> lemma_node_base t i nm
          | Some (CS.NodeArray ids r), BaseSort _ -> lemma_node_array t i ids r
          | _, _ -> ()
        end
      end

(* ---------------------------------------------------------------------- *)
(* 2. The Skolem typing gate on scope ids                                   *)
(* ---------------------------------------------------------------------- *)

(* `SDS.deps_typed` at the scope of ids `sc` (of length `len`, the units of
   one dependency's walk): each dependency names a position of the scope, whose
   id denotes the dependency's sort. *)
let rec deps_typed_ids (t:CS.sort_table) (sc:list nat) (len:nat) (deps:list SK.dependency) (work:nat)
  : Tot (option (bool & nat)) (decreases deps) =
  match deps with
  | [] -> Some (true, work)
  | (n, ty) :: rest ->
    if work < len + 1 then None
    else
      let w = work - (len + 1) in
      (match W.nth_id sc n with
       | None -> Some (false, w)
       | Some j ->
         (match sort_matches t w [MPair j ty] with
          | Some (true, w') -> deps_typed_ids t sc len rest w'
          | Some (false, w') -> Some (false, w')
          | None -> None))

(* `NR.all_typed` at the scopes of ids. *)
let rec scopes_typed_ids (t:CS.sort_table) (scopes:list (list nat)) (deps:list SK.dependency) (work:nat)
  : Tot (option (bool & nat)) (decreases scopes) =
  match scopes with
  | [] -> Some (true, work)
  | sc :: rest ->
    (match W.count_within work 0 sc with
     | None -> None
     | Some (len, w) ->
       (match deps_typed_ids t sc len deps w with
        | Some (true, w') -> scopes_typed_ids t rest deps w'
        | r -> r))

let rec lemma_nth_below (sc:list nat) (n bound j:nat)
  : Lemma (requires CS.all_below sc bound /\ W.nth_id sc n == Some j) (ensures j < bound) (decreases sc)
  = match sc with
    | _ :: rest -> if n > 0 then lemma_nth_below rest (n - 1) bound j
    | [] -> ()

let rec lemma_deps_typed_ids (t:CS.sort_table{CS.valid_table t}) (sc:list nat) (len:nat)
                             (deps:list SK.dependency) (work:nat)
  : Lemma (requires CS.all_below sc t.CS.node_count)
          (ensures (match deps_typed_ids t sc len deps work with
                    | Some (b, _) -> b == SDS.deps_typed (L.map (CS.interp_node t) sc) deps
                    | None -> True))
          (decreases deps)
  = match deps with
    | [] -> ()
    | (n, ty) :: rest ->
      if work >= len + 1 then begin
        let w = work - (len + 1) in
        W.lemma_nth_id (CS.interp_node t) sc n;
        match W.nth_id sc n with
        | None -> ()
        | Some j ->
          lemma_nth_below sc n t.CS.node_count j;
          lemma_sort_matches t w [MPair j ty];
          (match sort_matches t w [MPair j ty] with
           | Some (true, w') -> lemma_deps_typed_ids t sc len rest w'
           | _ -> ())
      end

let rec lemma_scopes_typed_ids (t:CS.sort_table{CS.valid_table t}) (scopes:list (list nat))
                               (deps:list SK.dependency) (work:nat)
  : Lemma (requires GP.scopes_below scopes t.CS.node_count)
          (ensures (match scopes_typed_ids t scopes deps work with
                    | Some (b, _) -> b == NR.all_typed (GP.interp_scopes t scopes) deps
                    | None -> True))
          (decreases scopes)
  = match scopes with
    | [] -> ()
    | sc :: rest ->
      W.lemma_count_within work 0 sc;
      (match W.count_within work 0 sc with
       | None -> ()
       | Some (len, w) ->
         lemma_deps_typed_ids t sc len deps w;
         (match deps_typed_ids t sc len deps w with
          | Some (true, w') -> lemma_scopes_typed_ids t rest deps w'
          | _ -> ()))

noeq
type gate_result =
  | GateOk : left:nat -> gate_result
  | GateFailed : gate_result
  | GateExhausted : gate_result

(* `NR.skolem_scopes_ok e j scopes` for the scopes of ids: only an open
   dependent step reads the scopes. *)
let skolem_gate (t:CS.sort_table) (e:U.binder_entry) (j:U.judgment) (scopes:list (list nat)) (work:nat)
  : gate_result =
  if e.U.binder_name <> "sk" then GateOk work
  else
    match NR.edge j with
    | None -> GateOk work
    | Some (lhs, rhs) ->
      if D.scoped [] lhs && D.scoped [] rhs then GateOk work
      else
        (match SK.definition_of lhs rhs with
         | Some d ->
           (match scopes_typed_ids t scopes d.SK.dependencies work with
            | Some (true, w) -> GateOk w
            | Some (false, _) -> GateFailed
            | None -> GateExhausted)
         | None -> GateFailed)

(* The gate agrees with the default's on the sorts the ids denote: it passes
   exactly when `NR.skolem_scopes_ok` does, unless its allowance is spent. *)
let lemma_skolem_gate (t:CS.sort_table{CS.valid_table t}) (e:U.binder_entry) (j:U.judgment)
                      (scopes:list (list nat)) (work:nat)
  : Lemma (requires GP.scopes_below scopes t.CS.node_count)
          (ensures (match skolem_gate t e j scopes work with
                    | GateOk _ -> NR.skolem_scopes_ok e j (GP.interp_scopes t scopes) == true
                    | GateFailed -> NR.skolem_scopes_ok e j (GP.interp_scopes t scopes) == false
                    | GateExhausted -> True))
  = if e.U.binder_name = "sk" then
      match NR.edge j with
      | None -> ()
      | Some (lhs, rhs) ->
        if D.scoped [] lhs && D.scoped [] rhs then ()
        else
          (match SK.definition_of lhs rhs with
           | Some d -> lemma_scopes_typed_ids t scopes d.SK.dependencies work
           | None -> ())

(* ---------------------------------------------------------------------- *)
(* 3. The replay's entry loop over the ids' demands                         *)
(* ---------------------------------------------------------------------- *)

noeq
type steps_result =
  | StepsOk : gate_left:nat -> steps_result
  | StepsRejected : steps_result
  | StepsGateExhausted : steps_result

(* `NR.steps_ok` with the demands of a checked guard's state: an entry is used
   when some scope id is assigned to it, its Skolem typing gate is `skolem_gate`
   at those ids (from `gate` units). Everything else, the local rule, the work
   charged per tree node and the premise sizes, is `NR.steps_ok`'s. *)
let rec steps_ok_checked (scoped:bool) (assertions:list expr) (count:nat) (gs:G.gstate)
                         (cache:I.index_tree U.judgment) (sizes:I.index_tree nat) (k:nat)
                         (entries:list U.binder_entry) (work gate:nat)
  : Tot steps_result (decreases entries) =
  match entries with
  | [] -> StepsOk gate
  | e :: rest ->
    let scopes = G.id_demanded gs.G.demands k in
    if Nil? scopes then steps_ok_checked scoped assertions count gs cache sizes (k + 1) rest work gate
    else
      match NR.nodes_within work [e.U.binder_formula] with
      | None -> StepsRejected
      | Some w1 ->
        let size : nat = if w1 <= work then work - w1 else 0 in
        (match NR.premise_charge sizes e.U.binder_premises w1 with
         | None -> StepsRejected
         | Some w2 ->
           let w3 = if e.U.binder_name = "sk" then (if count <= w2 then Some (w2 - count) else None) else Some w2 in
           (match w3, I.index_find cache k, I.opt_map_tail (I.index_find cache) e.U.binder_premises with
            | Some w, Some j, Some facts ->
              if NR.entry_ok scoped assertions e j facts then
                (match skolem_gate gs.G.graph.CT.sorts e j scopes gate with
                 | GateOk g ->
                   steps_ok_checked scoped assertions count gs cache (I.index_put sizes k size) (k + 1) rest w g
                 | GateFailed -> StepsRejected
                 | GateExhausted -> StepsGateExhausted)
              else StepsRejected
            | _, _, _ -> StepsRejected))

let lemma_map_nil (#a #b:Type) (f:a -> b) (l:list a)
  : Lemma (ensures (Nil? (L.map f l) <==> Nil? l)) = ()

(* A successful loop is the default loop at the demand table the ids denote. *)
let rec lemma_steps_checked (scoped:bool) (assertions:list expr) (count:nat) (gs:G.gstate)
                            (cache:I.index_tree U.judgment) (sizes:I.index_tree nat) (k:nat)
                            (entries:list U.binder_entry) (work gate:nat)
  : Lemma (requires GP.inv gs /\ StepsOk? (steps_ok_checked scoped assertions count gs cache sizes k entries work gate))
          (ensures NR.steps_ok scoped assertions count (GP.checked_demands gs) cache sizes k entries work)
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      let td = gs.G.demands in
      let tf = gs.G.graph.CT.sorts in
      let scopes = G.id_demanded td k in
      GP.lemma_demanded tf td k;
      lemma_map_nil (GP.interp_scope tf) scopes;
      if Nil? scopes then lemma_steps_checked scoped assertions count gs cache sizes (k + 1) rest work gate
      else
        match NR.nodes_within work [e.U.binder_formula] with
        | None -> ()
        | Some w1 ->
          let size : nat = if w1 <= work then work - w1 else 0 in
          (match NR.premise_charge sizes e.U.binder_premises w1 with
           | None -> ()
           | Some w2 ->
             let w3 = if e.U.binder_name = "sk" then (if count <= w2 then Some (w2 - count) else None) else Some w2 in
             (match w3, I.index_find cache k, I.opt_map_tail (I.index_find cache) e.U.binder_premises with
              | Some w, Some j, Some facts ->
                if NR.entry_ok scoped assertions e j facts then begin
                  assert (GP.scopes_below scopes tf.CS.node_count);
                  lemma_skolem_gate tf e j scopes gate;
                  match skolem_gate tf e j scopes gate with
                  | GateOk g ->
                    lemma_steps_checked scoped assertions count gs cache (I.index_put sizes k size) (k + 1) rest w g
                  | _ -> ()
                end
              | _, _, _ -> ()))

(* ---------------------------------------------------------------------- *)
(* 4. The cache the replay builds is the classified one                     *)
(* ---------------------------------------------------------------------- *)

(* `NR.judgments_of` builds, for every entry, the classification of the
   entry's own formula (`DGP.cache_classified`), which is what the checked
   guards read, and keeps the earlier entries. *)
let rec lemma_judgments_classified (entries:list U.binder_entry) (cache:I.index_tree U.judgment) (k:nat)
  : Lemma (ensures (match NR.judgments_of entries cache k with
                    | Some cache' ->
                      DGP.cache_classified cache' k entries /\
                      (forall (q:nat). q < k ==> I.index_find cache' q == I.index_find cache q)
                    | None -> True))
          (decreases entries)
  = match entries with
    | [] -> ()
    | e :: rest ->
      (match U.classify_fact e.U.binder_formula with
       | Some concl ->
         let cache1 = I.index_put cache k concl in
         lemma_judgments_classified rest cache1 (k + 1);
         let aux (q:nat) : Lemma (I.index_find cache1 q == (if q = k then Some concl else I.index_find cache q))
           = I.lemma_index_put cache k concl q in
         FStar.Classical.forall_intro aux
       | None -> ())

(* ---------------------------------------------------------------------- *)
(* 5. The guards' states                                                    *)
(* ---------------------------------------------------------------------- *)

(* What `lemma_dag_guard` establishes, and that the guard's final state is
   invariant: a valid sort table and demands over its ids. *)
let lemma_dag_guard_state (budget:G.resource_budget) (cg:CG.cgraph) (c:U.binder_certificate)
                          (cache:I.index_tree U.judgment) (handles:list nat)
  : Lemma (requires CG.graph_inv cg /\ DGP.handles_ok cg c.U.binder_entries handles /\
                    DGP.cache_classified cache 0 c.U.binder_entries /\
                    DG.DagChecked? (DG.dag_guard budget cg c cache handles))
          (ensures (let ds = DG.DagChecked?.state (DG.dag_guard budget cg c cache handles) in
                    let t = GP.checked_demands ds.DG.gs in
                    GP.inv ds.DG.gs /\
                    0 <= c.U.binder_root /\ c.U.binder_root < L.length c.U.binder_entries /\
                    L.memP [] (U.scope_demanded t c.U.binder_root) /\
                    BS.entries_scoped t cache 0 c.U.binder_entries))
  = DGP.lemma_dag_guard budget cg c cache handles;
    let gs0 = DG.initial budget cg in
    DGP.lemma_initial budget cg;
    GP.lemma_backward_from gs0 c;
    let G.Go _ gs1 = G.backward_from gs0 c in
    GP.lemma_root_at_empty gs1 c.U.binder_root;
    let G.Go () gs2 = G.root_at_empty gs1 c.U.binder_root in
    let td = gs2.G.demands in
    let t1 = gs2.G.graph.CT.sorts in
    DGP.lemma_start cg gs2;
    let ds0 = { DG.gs = gs2; DG.scopes = DS.empty_scopes; DG.memo = I.Empty } in
    DGP.lemma_entries_checked cg t1 td ds0 cache 0 c.U.binder_entries handles

let lemma_sorts_guard_state (budget:G.resource_budget) (c:U.binder_certificate) (cache:I.index_tree U.judgment)
  : Lemma (requires G.Checked? (G.verified_guard budget c cache))
          (ensures (let st = G.Checked?.state (G.verified_guard budget c cache) in
                    let t = GP.checked_demands st in
                    GP.inv st /\
                    0 <= c.U.binder_root /\ c.U.binder_root < L.length c.U.binder_entries /\
                    L.memP [] (U.scope_demanded t c.U.binder_root) /\
                    BS.entries_scoped t cache 0 c.U.binder_entries))
  = GP.lemma_verified_guard budget c cache;
    GP.lemma_backward budget c;
    let G.Go _ st1 = G.backward budget c in
    GP.lemma_root_at_empty st1 c.U.binder_root;
    let G.Go () st2 = G.root_at_empty st1 c.U.binder_root in
    CT.lemma_table_grows_refl st1.G.graph.CT.sorts;
    GP.lemma_entries_checked st1.G.graph.CT.sorts st1.G.demands st2 cache 0 c.U.binder_entries


(* ---------------------------------------------------------------------- *)
(* 6. The replay with a checked guard                                       *)
(* ---------------------------------------------------------------------- *)

(* Why a replay is, or is not, applied: an additive reason beside the
   verdict. `DefaultRoute` is the unchanged `NR.replay`. A selected opt-in
   route that does not apply leaves the node pending (`Unreplayed`) with the
   phase that stopped it; the default guard never runs in its place. *)
noeq
type outcome =
  | DefaultRoute : outcome
  | NotConsumed : outcome
  | MalformedPremises : outcome
  | EntriesUnclassified : outcome
  | RootMismatch : outcome
  | Unprepared : why:DD.unprepared_reason -> outcome
  | GuardRefused : outcome
  | GuardExhausted : phase:CT.phase -> outcome
  | SkolemTypingExhausted : outcome
  | StepsFailed : left:G.resource_budget -> outcome
  | GuardChecked : left:G.resource_budget -> outcome

noeq
type result = { verdict: NR.verdict; outcome: outcome }

let unreplayed (o:outcome) : result = { verdict = NR.Unreplayed; outcome = o }

(* The verdict once a checked guard has run: `left` is what the guard left,
   with the validation allowance the Skolem typing gate spent. *)
let finish (steps:steps_result) (left:G.resource_budget) : result =
  match steps with
  | StepsOk g -> { verdict = NR.Replayed; outcome = GuardChecked ({ left with G.validation = g }) }
  | StepsRejected -> unreplayed (StepsFailed left)
  | StepsGateExhausted -> unreplayed SkolemTypingExhausted

(* `NR.replay` on the prepared certificate of `verified-dag-v1`: the entries'
   own classification (`NR.judgments_of`) is the cache, `Z3DagGuard.dag_guard`
   (no `check_binder_entries`, no old budget) runs on it and the marshaler's
   handles, then the replay's entry loop reads the demands of the guard's
   state. The guard's budget is `b`. *)
let replay_dag (b:G.resource_budget) (assertions:list expr) (p:DD.prepared) (concl:U.judgment) : result =
  let c = p.DD.pcert in
  if not (NR.consumed_root c) then unreplayed NotConsumed
  else if not (NR.well_indexed c.U.binder_entries 0) then { verdict = NR.Malformed; outcome = MalformedPremises }
  else
    let n = U.count_cells 0 c.U.binder_entries in
    match NR.judgments_of c.U.binder_entries I.Empty 0 with
    | None -> unreplayed EntriesUnclassified
    | Some cache ->
      if not (0 <= c.U.binder_root && c.U.binder_root < n && I.index_find cache c.U.binder_root = Some concl)
      then unreplayed RootMismatch
      else
        match DG.dag_guard b p.DD.pgraph c cache p.DD.phandles with
        | DG.DagRefused -> unreplayed GuardRefused
        | DG.DagExhausted ph -> unreplayed (GuardExhausted ph)
        | DG.DagChecked ds ->
          finish (steps_ok_checked (NR.quant_intro_root c) assertions (U.count_cells 0 assertions) ds.DG.gs cache
                    I.Empty 0 c.U.binder_entries (U.binder_work_limit n) ds.DG.gs.G.valid)
                 (G.left_of ds.DG.gs)

(* The same with the guard of `verified-sorts-v1` (no companion: it prepares
   each entry's judgment from the cache). *)
let replay_sorts (b:G.resource_budget) (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment) : result =
  if not (NR.consumed_root c) then unreplayed NotConsumed
  else if not (NR.well_indexed c.U.binder_entries 0) then { verdict = NR.Malformed; outcome = MalformedPremises }
  else
    let n = U.count_cells 0 c.U.binder_entries in
    match NR.judgments_of c.U.binder_entries I.Empty 0 with
    | None -> unreplayed EntriesUnclassified
    | Some cache ->
      if not (0 <= c.U.binder_root && c.U.binder_root < n && I.index_find cache c.U.binder_root = Some concl)
      then unreplayed RootMismatch
      else
        match G.verified_guard b c cache with
        | G.Refused _ -> unreplayed GuardRefused
        | G.Exhausted ph -> unreplayed (GuardExhausted ph)
        | G.Checked st ->
          finish (steps_ok_checked (NR.quant_intro_root c) assertions (U.count_cells 0 assertions) st cache
                    I.Empty 0 c.U.binder_entries (U.binder_work_limit n) st.G.valid)
                 (G.left_of st)

(* ---------------------------------------------------------------------- *)
(* 7. The theorems                                                          *)
(* ---------------------------------------------------------------------- *)

(* A replay by the DAG guard states what `NR.lemma_replay` states of the
   default replay, in the same typed Root model: the root is scoped at `[]`
   and holds in every model of the quantifier laws that makes the assertions
   true. The prepared certificate `p` is an input of any origin that the
   type `DD.prepared` admits: its graph and handles are earned by the
   builders, the guard and the loop run on its own entries, and the
   conclusion is the root of its own classified cache. *)
let lemma_replay_dag (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                     (eq:ST.scalar_model base) (other:V.interpretation base (S.signature s))
                     (b:G.resource_budget) (assertions:list expr) (p:DD.prepared) (concl:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    ST.truths s bc eq other assertions /\
                    (replay_dag b assertions p concl).verdict == NR.Replayed)
          (ensures BS.binder_judgment_scoped [] concl /\
                   NR.holds_at s bc eq other [] (ST.empty_environment (S.signature s)) concl)
  = let c = p.DD.pcert in
    let entries = c.U.binder_entries in
    let n = U.count_cells 0 entries in
    let root = c.U.binder_root in
    match NR.judgments_of entries I.Empty 0 with
    | None -> ()
    | Some cache ->
      lemma_judgments_classified entries I.Empty 0;
      (match DG.dag_guard b p.DD.pgraph c cache p.DD.phandles with
       | DG.DagChecked ds ->
         lemma_dag_guard_state b p.DD.pgraph c cache p.DD.phandles;
         let t = GP.checked_demands ds.DG.gs in
         BS.lemma_count_cells 0 entries;
         lemma_steps_checked (NR.quant_intro_root c) assertions (U.count_cells 0 assertions) ds.DG.gs cache
           I.Empty 0 entries (U.binder_work_limit n) ds.DG.gs.G.valid;
         NR.lemma_steps s bc eq other (NR.quant_intro_root c) assertions (U.count_cells 0 assertions) t cache
           I.Empty 0 entries (U.binder_work_limit n);
         let key : nat = root in
         assert (NR.entry_valid s bc eq other t cache key);
         NR.lemma_entry_valid_def s bc eq other t cache key;
         BS.lemma_scoped_at t cache entries key []
       | _ -> ())

let lemma_replay_sorts (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:ST.scalar_model base) (other:V.interpretation base (S.signature s))
                       (b:G.resource_budget) (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    ST.truths s bc eq other assertions /\
                    (replay_sorts b assertions c concl).verdict == NR.Replayed)
          (ensures BS.binder_judgment_scoped [] concl /\
                   NR.holds_at s bc eq other [] (ST.empty_environment (S.signature s)) concl)
  = let entries = c.U.binder_entries in
    let n = U.count_cells 0 entries in
    let root = c.U.binder_root in
    match NR.judgments_of entries I.Empty 0 with
    | None -> ()
    | Some cache ->
      (match G.verified_guard b c cache with
       | G.Checked st ->
         lemma_sorts_guard_state b c cache;
         let t = GP.checked_demands st in
         BS.lemma_count_cells 0 entries;
         lemma_steps_checked (NR.quant_intro_root c) assertions (U.count_cells 0 assertions) st cache
           I.Empty 0 entries (U.binder_work_limit n) st.G.valid;
         NR.lemma_steps s bc eq other (NR.quant_intro_root c) assertions (U.count_cells 0 assertions) t cache
           I.Empty 0 entries (U.binder_work_limit n);
         let key : nat = root in
         assert (NR.entry_valid s bc eq other t cache key);
         NR.lemma_entry_valid_def s bc eq other t cache key;
         BS.lemma_scoped_at t cache entries key []
       | _ -> ())

(* ---------------------------------------------------------------------- *)
(* 8. The route of a node                                                   *)
(* ---------------------------------------------------------------------- *)

(* The guard a document selects for the certificates of its nodes. `Default`
   is the unchanged replay; `SortsV1` and `DagV1` are the opt-in modes, the
   latter with the preparation the marshaler recorded for the node. *)
noeq
type route =
  | Default : route
  | SortsV1 : route
  | DagV1 : prep:DD.preparation -> route

(* `NR.replay` of the node's certificate `c` under `r`. A route other than
   the default first applies the default's two shape checks to `c` itself
   (a consumed root, premises that are earlier entries), so a malformed
   certificate is rejected, and an unconsumed one left pending, exactly as by
   default. An opt-in route whose preparation is missing leaves the node
   pending with the reason; the default guard is never a fallback. *)
let replay_route (r:route) (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment) : result =
  match r with
  | Default -> { verdict = NR.replay assertions c concl; outcome = DefaultRoute }
  | _ ->
    if not (NR.consumed_root c) then unreplayed NotConsumed
    else if not (NR.well_indexed c.U.binder_entries 0) then { verdict = NR.Malformed; outcome = MalformedPremises }
    else
      (match r with
       | SortsV1 -> replay_sorts (G.verified_budget (U.count_cells 0 c.U.binder_entries)) assertions c concl
       | DagV1 (DD.Ready p _) ->
         replay_dag (DD.dag_budget (U.count_cells 0 p.DD.pcert.U.binder_entries)) assertions p concl
       | DagV1 (DD.Unready why _) -> unreplayed (Unprepared why)
       | Default -> unreplayed NotConsumed)

let lemma_replay_route (#base:sort -> Type0) (s:S.checked_schema) (bc:S.boolean_carrier base)
                       (eq:ST.scalar_model base) (other:V.interpretation base (S.signature s))
                       (r:route) (assertions:list expr) (c:U.binder_certificate) (concl:U.judgment)
  : Lemma (requires Q.forall_model s bc other /\ E.exists_model s bc other /\
                    ST.truths s bc eq other assertions /\
                    (replay_route r assertions c concl).verdict == NR.Replayed)
          (ensures BS.binder_judgment_scoped [] concl /\
                   NR.holds_at s bc eq other [] (ST.empty_environment (S.signature s)) concl)
  = match r with
    | Default -> NR.lemma_replay s bc eq other assertions c concl
    | SortsV1 ->
      if NR.consumed_root c && NR.well_indexed c.U.binder_entries 0 then
        lemma_replay_sorts s bc eq other (G.verified_budget (U.count_cells 0 c.U.binder_entries)) assertions c concl
    | DagV1 (DD.Ready p _) ->
      if NR.consumed_root c && NR.well_indexed c.U.binder_entries 0 then
        lemma_replay_dag s bc eq other (DD.dag_budget (U.count_cells 0 p.DD.pcert.U.binder_entries)) assertions p concl
    | DagV1 (DD.Unready _ _) -> ()
