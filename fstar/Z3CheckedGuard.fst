(*
   Z3CheckedGuard.fst

   The scope guard of binder certificates in the opt-in, experimental
   accounting mode `verified-sorts-v1` (checked sort ids and a checked
   scope-shape graph; no expression sharing and no scope memo). It runs the algorithm of `Z3UnifiedProof.binder_scoped`
   (scopes demanded backwards from the root at `[]`, premises earlier
   entries, an introduction's premises at its binder sorts reversed in front
   of the user's scope; then every demanded scope of every entry checked
   forwards, premises included) on checked representations:

   * scopes are lists of checked sort ids and are compared by id, which is
     sort equality (`Z3CheckedSorts.lemma_id_equal`);
   * an entry's judgment is prepared once (`Z3CheckedTerms.prepare_expr`),
     only when some scope is demanded for it, and then walked at each of its
     scopes (`Z3CheckedScope.walk`); its binder sorts are interned once per
     pass.

   Three budgets, charged before the step they pay for, replace the old
   single work count (`resource_budget`): Preparation (sort and expression
   preparation, `Z3CheckedTerms`), Validation (walks, scope comparisons,
   lookups) and Storage (cells allocated, never refunded). The structural
   caps of the old guard stay: `binder_scope_limit` sorts per demanded
   scope, `binder_entry_scope_limit` scopes per entry and
   `binder_demand_limit n` assignments; exceeding one is exhaustion
   (`Storage`), not a structural refusal. A premise that is not an earlier
   entry, an entry without a judgment, a failed scope or premise check and a
   root without `[]` are refusals.

   `Z3CheckedGuardProof.lemma_verified_guard`: a `Checked` result establishes
   `Z3BinderScope.entries_scoped` and the root at `[]` for the demand table the
   ids denote, the specification the old guard's success establishes. Nothing
   is cached across certificates; a refused or exhausted run yields no
   success.
*)
module Z3CheckedGuard

open Z3AstTheory
open Z3UnifiedProof
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module T = Z3CheckedTerms
module W = Z3CheckedScope
module SK = Z3Skolemization

type resource_budget = { preparation: nat; validation: nat; storage: nat }

type id_demands = I.index_tree (list (list nat))

let id_demanded (t:id_demands) (k:int) : list (list nat) =
  match I.index_find t k with
  | Some scopes -> scopes
  | None -> []

noeq
type gstate = {
  graph: T.term_graph;
  demands: id_demands;
  prep: nat;
  valid: nat;
  store: nat;
}

type failure =
  | Exhaust : phase:T.phase -> failure
  | Refuse

noeq
type step (a:Type) =
  | Go : value:a -> st:gstate -> step a
  | Stop : reason:failure -> step a

let spend_valid (st:gstate) (n:nat) : option gstate =
  if n <= st.valid then Some ({ st with valid = st.valid - n }) else None

(* --- Scopes of ids ------------------------------------------------------------------------- *)

(* `a = b`, one unit per cell compared. *)
let rec ids_eq (work:nat) (a b:list nat) : Tot (option (bool & nat)) (decreases a) =
  if work = 0 then None
  else
    match a, b with
    | [], [] -> Some (true, work - 1)
    | x :: a', y :: b' -> if x = y then ids_eq (work - 1) a' b' else Some (false, work - 1)
    | _, _ -> Some (false, work - 1)

(* `L.mem s scopes`. *)
let rec scope_mem (work:nat) (s:list nat) (scopes:list (list nat)) : Tot (option (bool & nat)) (decreases scopes) =
  match scopes with
  | [] -> Some (false, work)
  | x :: rest ->
    (match ids_eq work x s with
     | Some (true, w) -> Some (true, w)
     | Some (false, w) -> scope_mem w s rest
     | None -> None)

(* The binder sort ids of an entry, interned (Preparation). *)
let entry_binders (st:gstate) (e:binder_entry) : step (option (list nat)) =
  match e.binder_sorts with
  | None -> Go None st
  | Some bs ->
    (match T.intern_sorts st.graph.T.sorts bs st.prep st.store with
     | T.SortsExhausted p -> Stop (Exhaust p)
     | T.SortsInterned t ids _ w s ->
       Go (Some ids) ({ st with graph = { st.graph with T.sorts = t }; prep = w; store = s }))

(* The scope of an entry's premises when it is used at `scope` of length `len`. *)
let premise_scope (st:gstate) (bids:option (list nat)) (scope:list nat) (len:nat) : step (list nat & nat) =
  match bids with
  | None -> Go (scope, len) st
  | Some bs ->
    (match W.count_within st.valid 0 bs with
     | None -> Stop (Exhaust T.Validation)
     | Some (m, v) ->
       if m + len > binder_scope_limit then Stop (Exhaust T.Storage)
       else if v < m + 1 then Stop (Exhaust T.Validation)
       else if st.store < m then Stop (Exhaust T.Storage)
       else Go (W.under bs scope, m + len) ({ st with valid = v - (m + 1); store = st.store - m }))

(* --- The backward pass: demanded scopes ------------------------------------------------------- *)

(* Assign `scope` to entry `k`; `count` assignments are left. *)
let demand (st:gstate) (k:nat) (scope:list nat) (count:nat) : step nat =
  match spend_valid st (1 + CS.table_units) with
  | None -> Stop (Exhaust T.Validation)
  | Some st0 ->
    let old = id_demanded st0.demands k in
    (match scope_mem st0.valid scope old with
     | None -> Stop (Exhaust T.Validation)
     | Some (true, v) -> Go count ({ st0 with valid = v })
     | Some (false, v) ->
       (match W.count_within v 0 old with
        | None -> Stop (Exhaust T.Validation)
        | Some (m, v') ->
          if count = 0 || m >= binder_entry_scope_limit then Stop (Exhaust T.Storage)
          else if v' < CS.table_units then Stop (Exhaust T.Validation)
          else if st0.store < 2 + CS.table_units then Stop (Exhaust T.Storage)
          else Go (count - 1) ({ st0 with demands = I.index_put st0.demands k (scope :: old);
                                          valid = v' - CS.table_units;
                                          store = st0.store - (2 + CS.table_units) })))

let rec demand_premises (st:gstate) (k:int) (ps:list int) (scope:list nat) (count:nat)
  : Tot (step nat) (decreases ps) =
  match ps with
  | [] -> Go count st
  | p :: rest ->
    if 0 <= p && p < k then
      (match demand st p scope count with
       | Go c st' -> demand_premises st' k rest scope c
       | Stop f -> Stop f)
    else Stop Refuse

let rec demand_entry (st:gstate) (k:int) (bids:option (list nat)) (ps:list int) (scopes:list (list nat)) (count:nat)
  : Tot (step nat) (decreases scopes) =
  match scopes with
  | [] -> Go count st
  | s :: rest ->
    (match W.count_within st.valid 0 s with
     | None -> Stop (Exhaust T.Validation)
     | Some (len, v) ->
       (match premise_scope ({ st with valid = v }) bids s len with
        | Stop f -> Stop f
        | Go (s', _) st1 ->
          (match demand_premises st1 k ps s' count with
           | Go c st2 -> demand_entry st2 k bids ps rest c
           | Stop f -> Stop f)))

(* `reversed` lists the entries last first; `k` is the index of its head. *)
let rec demand_entries (st:gstate) (k:int) (reversed:list binder_entry) (count:nat)
  : Tot (step unit) (decreases reversed) =
  match reversed with
  | [] -> Go () st
  | e :: rest ->
    (match spend_valid st (1 + CS.table_units) with
     | None -> Stop (Exhaust T.Validation)
     | Some st0 ->
       (match id_demanded st0.demands k with
        | [] -> demand_entries st0 (k - 1) rest count
        | scopes ->
          (match entry_binders st0 e with
           | Stop f -> Stop f
           | Go bids st1 ->
             (match demand_entry st1 k bids e.binder_premises scopes count with
              | Go c st2 -> demand_entries st2 (k - 1) rest c
              | Stop f -> Stop f))))

(* --- The forward pass: every demanded scope checked ------------------------------------------ *)

let judgment_exprs (j:judgment) : list expr =
  match j with
  | Holds e -> [e]
  | Equal a b | Observational a b -> [a; b]

(* The nodes of `es`, prepared in order. *)
let rec prepare_list (st:gstate) (es:list expr) (acc:list nat) : Tot (step (list nat)) (decreases es) =
  match es with
  | [] -> Go (L.rev acc) st
  | e :: rest ->
    if st.store < 2 then Stop (Exhaust T.Storage)
    else
      (match T.prepare_expr st.graph e st.prep (st.store - 2) with
       | T.PrepExhausted p -> Stop (Exhaust p)
       | T.Prepared g x _ w s -> prepare_list ({ st with graph = g; prep = w; store = s }) rest (x :: acc))

let rec premises_checked (st:gstate) (k:int) (ps:list int) (scope:list nat) : Tot (step unit) (decreases ps) =
  match ps with
  | [] -> Go () st
  | p :: rest ->
    if 0 <= p && p < k then
      (match spend_valid st (1 + CS.table_units) with
       | None -> Stop (Exhaust T.Validation)
       | Some st0 ->
         (match scope_mem st0.valid scope (id_demanded st0.demands p) with
          | Some (true, v) -> premises_checked ({ st0 with valid = v }) k rest scope
          | Some (false, _) -> Stop Refuse
          | None -> Stop (Exhaust T.Validation)))
    else Stop Refuse

let rec entry_checked (st:gstate) (k:int) (bids:option (list nat)) (ps:list int) (xs:list nat)
                      (scopes:list (list nat))
  : Tot (step unit) (decreases scopes) =
  match scopes with
  | [] -> Go () st
  | s :: rest ->
    (match W.count_within st.valid 0 s with
     | None -> Stop (Exhaust T.Validation)
     | Some (len, v) ->
       (match W.check_scoped st.graph s len xs v st.store with
        | W.WalkExhausted p -> Stop (Exhaust p)
        | W.Walked false _ _ -> Stop Refuse
        | W.Walked true v1 s1 ->
          (match premise_scope ({ st with valid = v1; store = s1 }) bids s len with
           | Stop f -> Stop f
           | Go (s', _) st1 ->
             (match premises_checked st1 k ps s' with
              | Go () st2 -> entry_checked st2 k bids ps xs rest
              | Stop f -> Stop f))))

(* Entry `k`, demanded at `scopes`: its judgment prepared, its binder sorts
   interned, every scope checked. *)
let entry_step (st:gstate) (k:nat) (e:binder_entry) (j:judgment) (scopes:list (list nat)) : step unit =
  match prepare_list st (judgment_exprs j) [] with
  | Stop f -> Stop f
  | Go xs st1 ->
    (match entry_binders st1 e with
     | Stop f -> Stop f
     | Go bids st2 -> entry_checked st2 k bids e.binder_premises xs scopes)

let rec entries_checked (st:gstate) (cache:I.index_tree judgment) (k:nat) (entries:list binder_entry)
  : Tot (step unit) (decreases entries) =
  match entries with
  | [] -> Go () st
  | e :: rest ->
    (match spend_valid st (1 + CS.table_units) with
     | None -> Stop (Exhaust T.Validation)
     | Some st0 ->
       (match I.index_find cache k with
        | None -> Stop Refuse
        | Some j ->
          (match id_demanded st0.demands k with
           | [] -> entries_checked st0 cache (k + 1) rest
           | scopes ->
             (match entry_step st0 k e j scopes with
              | Go () st3 -> entries_checked st3 cache (k + 1) rest
              | Stop f -> Stop f))))

(* --- The guard --------------------------------------------------------------------------------- *)

noeq
type guard_result =
  | Checked : state:gstate -> guard_result
  | Refused : state:gstate -> guard_result
  | Exhausted : phase:T.phase -> guard_result

let initial (budget:resource_budget) : gstate =
  { graph = T.empty_graph; demands = I.Empty;
    prep = budget.preparation; valid = budget.validation; store = budget.storage }

(* The backward pass from the root at `[]`: counting and reversing the
   entries (one validation unit and one storage cell per entry), the root's
   assignment `[[]]`, then the demands of every entry, last first. *)
let backward_from (st:gstate) (c:binder_certificate) : step nat =
  let root = c.binder_root in
  match W.count_within st.valid 0 c.binder_entries with
  | None -> Stop (Exhaust T.Validation)
  | Some (n, v) ->
    if not (0 <= root && root < n) then Stop Refuse
    else if st.store < n + 2 + CS.table_units then Stop (Exhaust T.Storage)
    else if v < CS.table_units then Stop (Exhaust T.Validation)
    else
      let st0 = { st with demands = I.index_put I.Empty root [[]]; valid = v - CS.table_units;
                          store = st.store - (n + 2 + CS.table_units) } in
      match demand_entries st0 (n - 1) (L.rev c.binder_entries) (binder_demand_limit n) with
      | Go () st1 -> Go n st1
      | Stop f -> Stop f

let backward (budget:resource_budget) (c:binder_certificate) : step nat = backward_from (initial budget) c

(* The root is demanded at `[]`. *)
let root_at_empty (st:gstate) (root:int) : step unit =
  match spend_valid st CS.table_units with
  | None -> Stop (Exhaust T.Validation)
  | Some st2 ->
    (match scope_mem st2.valid [] (id_demanded st2.demands root) with
     | None -> Stop (Exhaust T.Validation)
     | Some (false, _) -> Stop Refuse
     | Some (true, v) -> Go () ({ st2 with valid = v }))

let verified_guard (budget:resource_budget) (c:binder_certificate) (cache:I.index_tree judgment)
  : guard_result =
  match backward budget c with
  | Stop Refuse -> Refused (initial budget)
  | Stop (Exhaust p) -> Exhausted p
  | Go _ st1 ->
    (match root_at_empty st1 c.binder_root with
     | Stop Refuse -> Refused st1
     | Stop (Exhaust p) -> Exhausted p
     | Go () st2 ->
       (match entries_checked st2 cache 0 c.binder_entries with
        | Go () st3 -> Checked st3
        | Stop Refuse -> Refused st2
        | Stop (Exhaust p) -> Exhausted p))

(* --- Budgets of the mode -------------------------------------------------------------------------- *)

(* PROVISIONAL budgets of an experimental mode, not final defaults: a certificate with `n`
   entries gets `n + 1` shares of 2^16 units in each phase, a cap no larger per phase than the old
   guard's per-entry allowance (`binder_work_limit`). The units differ from the old ones; this is
   not an equivalence, and the three phases together allow up to three times the old abstract
   work. This mode prepares every demanded entry's judgment as a tree and reads every sort
   occurrence: on the NNF task's guard-budget certificates its preparation alone needs 2.7 to 6.0
   times and its three budgets 3.9 to 8.5 times the old guard's units, with 3.9 to 10.8 times the
   CPU and 2 to 110 times the peak memory (PulseCore.Action-1 query 1 node 433 needs 366,083
   preparation units per share), so it is not the resource fix and admits none of them at these
   budgets. The default checker mode is unchanged and never selects it. *)
let verified_preparation_per_entry : nat = 65536
let verified_validation_per_entry : nat = 65536
let verified_storage_per_entry : nat = 65536

let verified_budget (n:nat) : resource_budget = {
  preparation = verified_preparation_per_entry * (n + 1);
  validation = verified_validation_per_entry * (n + 1);
  storage = verified_storage_per_entry * (n + 1);
}

(* --- The checker with the verified guard ------------------------------------------------------------ *)

type binder_outcome =
  | BinderEntriesFailed
  | BinderGuardChecked : left:resource_budget -> binder_outcome
  | BinderGuardRefused : left:resource_budget -> binder_outcome
  | BinderGuardExhausted : phase:T.phase -> binder_outcome
  | BinderUnprepared

let left_of (st:gstate) : resource_budget = { preparation = st.prep; validation = st.valid; storage = st.store }

let verify_binder (skolems:list SK.definition) (assertions:list judgment)
                  (certificate:binder_certificate) (concl:judgment) : binder_outcome =
  match check_binder_entries skolems assertions certificate.binder_entries I.Empty 0 with
  | None -> BinderEntriesFailed
  | Some cache ->
    if I.index_find cache certificate.binder_root <> Some concl then BinderEntriesFailed
    else
      let n = count_cells 0 certificate.binder_entries in
      match verified_guard (verified_budget n) certificate cache with
      | Checked st -> BinderGuardChecked (left_of st)
      | Refused st -> BinderGuardRefused (left_of st)
      | Exhausted p -> BinderGuardExhausted p

let check_binder_verified (skolems:list SK.definition) (assertions:list judgment)
                          (certificate:binder_certificate) (concl:judgment) : bool =
  BinderGuardChecked? (verify_binder skolems assertions certificate concl)

(* `check_node_with_membership` with the verified guard for quantifier
   introductions; every other node is checked by it. *)
let check_node_verified (skolems:list SK.definition) (strict:bool) (assertions:list judgment)
                        (contains:judgment -> bool) (node:proof_node)
  : option (checked_fact & nat) & option binder_outcome =
  match node.kind with
  | QuantifierIntroduction certificate ->
    let facts = premise_judgments node.premises in
    if well_formed node.conclusion && judgments_wf facts && scopes_wf node.premises &&
       facts = [] && Some? (relational node.conclusion)
    then
      let outcome = verify_binder skolems assertions certificate node.conclusion in
      Some ({ conclusion = node.conclusion; hypotheses = [] }, (if BinderGuardChecked? outcome then 0 else 1)),
      Some outcome
    else None, None
  | _ -> check_node_with_membership skolems strict assertions contains node, None
