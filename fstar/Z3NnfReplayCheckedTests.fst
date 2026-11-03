(*
   Z3NnfReplayCheckedTests.fst

   Executable tests of the replay with a checked guard (`Z3NnfReplayChecked`),
   each a function returning `true`, run natively (the OCaml driver
   `test_nrc.ml` and, through `Z3CherryTests.run`, the Cherry checker) and
   verified with the F* test modules. Certificates are prepared the way the
   marshaler prepares them: the `Z3DagDocument` builders and
   `prepare_certificate` on a checked graph (`prepare` below installs the
   expressions of a certificate by native ids it chooses; the diamond is
   built by hand so that its terms are shared in the graph). Nothing here
   fabricates a `Z3DagDocument.prepared` by record syntax.

   A. The same certificate is pending by default and replayed by the DAG
      guard: a shared diamond over a long-named sort (`diamond`), whose tree
      the default guard charges, for every sort comparison, the names'
      characters until its work is spent (`Z3NnfReplay.replay` is
      `Unreplayed`), while the old guard with an unbounded work limit
      accepts it (the structure is fine) and the checked graph guard walks
      each node once (`Replayed`, `GuardChecked`).
   B. Differential: small NNF and quantifier-introduction certificates, among
      them the BreakVC shape (two nested Term binders), have the verdict the
      default replay has, `Replayed`, `Unreplayed` or `Malformed`, through
      the DAG guard and the sorts guard.
   C. Negatives, each through the default and the DAG route: a wrong scope (a
      variable annotated with another sort, a name equal up to its native-id
      prefix, a domain order swap), a wrong premise, forward, self and
      negative premises, a wrong conclusion (the root), a companion of
      another certificate (`RootMismatch`), a preparation that is missing
      (`Unprepared`, pending, no fallback), the budgets exactly and one unit
      short in each phase.
   D. Open dependent Skolem steps: the FStar.Nonempty query 2 node 92
      certificate (the step is open at the scope [Term; Universe]) replays
      by default and by the DAG route with the closure, stays pending
      without; the typing gate `skolem_gate` agrees with
      `Z3NnfReplay.skolem_scopes_ok` on the sorts the ids denote, for
      reversed scopes, repeated sorts, array domains (order and arity), array
      ranges, nested arrays, short scopes and positions beyond the scope; the
      gate's exact units; a tampered demand (outside the guard's contract)
      is refused by the loop; a sort 50,000 arrays deep is matched against
      its id at the normal stack.
*)
module Z3NnfReplayCheckedTests

open Z3AstTheory
module U = Z3UnifiedProof
module NR = Z3NnfReplay
module NRC = Z3NnfReplayChecked
module I = Z3ProofIndex
module L = FStar.List.Tot
module CS = Z3CheckedSorts
module CT = Z3CheckedTerms
module G = Z3CheckedGuard
module CG = Z3CheckedGraph
module DG = Z3DagGuard
module DD = Z3DagDocument
module SK = Z3Skolemization
module R = Z3ResolutionProofTheory
module O = Z3ObservationalEquality
module BR = Z3BooleanRewrite
module SP = Z3SortedProof

(* ---------------------------------------------------------------------- *)
(* Shapes                                                                   *)
(* ---------------------------------------------------------------------- *)

let symbol (name:string) (ds:list sort) (r:sort) : func_decl =
  { decl_name = name; domain = ds; range = r; interp = None; int_params = [] }

let oeq (a b:expr) : expr = O.mk_oeq_expr a b
let eqe (a b:expr) : expr = R.mk_eq_expr a b
let neg (a:expr) : expr = R.mk_not_expr a
let forall_ (bs:list sort) (b:expr) : expr = Quantifier Forall_k bs bool_sort b
let mk_and (args:list expr) : expr = App (BR.connective_decl BR.Conjunction args) args
let mk_or (args:list expr) : expr = App (BR.connective_decl BR.Disjunction args) args

let be (name:string) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; U.binder_formula = f; U.binder_premises = ps; U.binder_sorts = None }
let bq (name:string) (bs:list sort) (f:expr) (ps:list int) : U.binder_entry =
  { U.binder_name = name; U.binder_formula = f; U.binder_premises = ps; U.binder_sorts = Some bs }
let refl (e:expr) : U.binder_entry = be "refl" (oeq e e) []
let cert (es:list U.binder_entry) (root:int) : U.binder_certificate =
  { U.binder_entries = es; U.binder_root = root }

let term : sort = BaseSort "Term"
let universe : sort = BaseSort "Universe"
let integer : sort = BaseSort "Int"

(* ---------------------------------------------------------------------- *)
(* Preparing a certificate on a checked graph                               *)
(* ---------------------------------------------------------------------- *)

(* A graph allowance far above any fixture's need. *)
let ample : nat = 1000000000

noeq
type inst = { ic: DD.ccache; next: nat }

let fresh (c:inst) : nat & inst = (c.next, { c with next = c.next + 1 })

let installed (c:inst) (r:DD.step DD.ccache) (nid:nat) : option (inst & nat) =
  match r with
  | DD.Built ic -> Some ({ c with ic = ic }, nid)
  | _ -> None

let rec install_sort (c:inst) (s:sort) : Tot (option (inst & nat)) (decreases s) =
  let (nid, c) = fresh c in
  match s with
  | BaseSort name -> installed c (DD.build_base_sort c.ic nid name) nid
  | ArraySort ds r ->
    (match install_sorts c ds [] with
     | Some (c1, dn) ->
       (match install_sort c1 r with
        | Some (c2, rn) -> installed c2 (DD.build_array_sort c2.ic nid dn rn) nid
        | None -> None)
     | None -> None)

and install_sorts (c:inst) (ss:list sort) (acc:list nat) : Tot (option (inst & list nat)) (decreases ss) =
  match ss with
  | [] -> Some (c, L.rev acc)
  | s :: rest ->
    (match install_sort c s with
     | Some (c1, n) -> install_sorts c1 rest (n :: acc)
     | None -> None)

let rec install_expr (c:inst) (e:expr) : Tot (option (inst & nat)) (decreases e) =
  match e with
  | Var n s ->
    (match install_sort c s with
     | Some (c1, sn) ->
       let (nid, c2) = fresh c1 in
       installed c2 (DD.build_var c2.ic nid n sn) nid
     | None -> None)
  | App f args ->
    (match install_exprs c args [] with
     | Some (c1, an) ->
       (match install_sort c1 f.range with
        | Some (c2, rn) ->
          let (dnid, c3) = fresh c2 in
          let (nid, c4) = fresh c3 in
          installed c4 (DD.build_app c4.ic nid dnid f.decl_name f.interp f.int_params an rn) nid
        | None -> None)
     | None -> None)
  | Quantifier k bs q b ->
    (match install_sorts c bs [] with
     | Some (c1, bn) ->
       (match install_expr c1 b with
        | Some (c2, yn) ->
          let (nid, c3) = fresh c2 in
          installed c3 (DD.build_quant c3.ic nid k bn yn) nid
        | None -> None)
     | None -> None)

and install_exprs (c:inst) (es:list expr) (acc:list nat) : Tot (option (inst & list nat)) (decreases es) =
  match es with
  | [] -> Some (c, L.rev acc)
  | e :: rest ->
    (match install_expr c e with
     | Some (c1, n) -> install_exprs c1 rest (n :: acc)
     | None -> None)

let rec install_entries (c:inst) (es:list U.binder_entry) (acc:list DD.raw_entry)
  : Tot (option (inst & list DD.raw_entry)) (decreases es) =
  match es with
  | [] -> Some (c, L.rev acc)
  | e :: rest ->
    (match install_expr c e.U.binder_formula with
     | Some (c1, fnid) ->
       let sorted : option (inst & option (list nat)) =
         (match e.U.binder_sorts with
          | None -> Some (c1, None)
          | Some bs -> (match install_sorts c1 bs [] with Some (c2, ns) -> Some (c2, Some ns) | None -> None)) in
       (match sorted with
        | Some (c2, ns) ->
          install_entries c2 rest
            ({ DD.raw_name = e.U.binder_name; DD.raw_formula = fnid; DD.raw_premises = e.U.binder_premises;
               DD.raw_sorts = ns } :: acc)
        | None -> None)
     | None -> None)

(* The prepared certificate the marshaler would record for `entries`. *)
let prepare (entries:list U.binder_entry) (root:int) : option DD.prepared =
  let c0 : inst = { ic = DD.with_budget DD.empty_cache ample ample; next = 1 } in
  match install_entries c0 entries [] with
  | Some (c1, raws) ->
    (match DD.prepare_certificate c1.ic raws root 0 with
     | DD.Built (_, p) -> Some p
     | _ -> None)
  | None -> None

(* The judgment of the certificate's root, from the cache the replay builds. *)
let own_conclusion (c:U.binder_certificate) : option U.judgment =
  match NR.judgments_of c.U.binder_entries I.Empty 0 with
  | Some cache -> I.index_find cache c.U.binder_root
  | None -> None

let budget_of (p:DD.prepared) : G.resource_budget =
  DD.dag_budget (U.count_cells 0 p.DD.pcert.U.binder_entries)

let dag (assertions:list expr) (p:DD.prepared) (j:U.judgment) : NRC.result =
  NRC.replay_dag (budget_of p) assertions p j

let is_checked (r:NRC.result) : bool = match r.NRC.outcome with NRC.GuardChecked _ -> true | _ -> false
let is_refused (r:NRC.result) : bool = match r.NRC.outcome with NRC.GuardRefused -> true | _ -> false
let is_exhausted (r:NRC.result) (ph:CT.phase) : bool =
  match r.NRC.outcome with NRC.GuardExhausted p -> p = ph | _ -> false

(* The default replay and the DAG replay of the same prepared certificate give
   the verdict `v`. *)
let both (assertions:list expr) (entries:list U.binder_entry) (root:int) (v:NR.verdict) : bool =
  match prepare entries root with
  | Some p ->
    (match own_conclusion p.DD.pcert with
     | Some j -> NR.replay assertions p.DD.pcert j = v && (dag assertions p j).NRC.verdict = v
     | None -> false)
  | None -> false

(* The sorts guard agrees on the same certificate (no companion). *)
let both_sorts (assertions:list expr) (entries:list U.binder_entry) (root:int) (v:NR.verdict) : bool =
  let c = cert entries root in
  match own_conclusion c with
  | Some j -> NR.replay assertions c j = v &&
              (NRC.replay_sorts (G.verified_budget (U.count_cells 0 entries)) assertions c j).NRC.verdict = v
  | None -> false

(* ---------------------------------------------------------------------- *)
(* A. The same certificate, pending by default, replayed by the DAG guard   *)
(* ---------------------------------------------------------------------- *)

type op =
  | OBase : nid:nat -> name:string -> op
  | OApp : nid:nat -> dnid:nat -> name:string -> tag:option decl_kind -> args:list nat -> range:nat -> op

let run_op (c:DD.ccache) (o:op) : DD.step DD.ccache =
  match o with
  | OBase nid name -> DD.build_base_sort c nid name
  | OApp nid dnid name tag args range -> DD.build_app c nid dnid name tag [] args range

let rec run_ops (c:DD.ccache) (ops:list op) : Tot (option DD.ccache) (decreases ops) =
  match ops with
  | [] -> Some c
  | o :: rest -> (match run_op c o with DD.Built c1 -> run_ops c1 rest | _ -> None)

(* s_0 = c0, s_(i+1) = h(s_i, s_i): node 11 + i is s_i. *)
let rec chain_ops (i k:nat) (acc:list op) : Tot (list op) (decreases k - i) =
  if i >= k then L.rev acc
  else chain_ops (i + 1) k (OApp (12 + i) 21 "h" None [11 + i; 11 + i] 1 :: acc)

let native_name : string = "sort!2147483829:Term"

(* D = P(s_k); the certificate refl (D ~ D); nnf-neg (not (not D) ~ D) [0]. The
   tree of s_k has 2^k leaves, its graph k + 1 nodes. *)
let diamond_ops (k:nat) (d_nid:nat) : list op =
  L.append [OBase 1 native_name; OBase 2 "Bool"; OApp 11 20 "c0" None [] 1]
    (L.append (chain_ops 0 k [])
       [OApp d_nid 22 "P" None [11 + k] 2;
        OApp (d_nid + 1) 23 "not" (Some Z3ValueTheory.op_not) [d_nid] 2;
        OApp (d_nid + 2) 23 "not" (Some Z3ValueTheory.op_not) [d_nid + 1] 2;
        OApp (d_nid + 3) 24 "~" (Some Z3ValueTheory.op_oeq) [d_nid; d_nid] 2;
        OApp (d_nid + 4) 24 "~" (Some Z3ValueTheory.op_oeq) [d_nid + 2; d_nid] 2])

let raw (name:string) (formula:nat) (premises:list int) : DD.raw_entry =
  { DD.raw_name = name; DD.raw_formula = formula; DD.raw_premises = premises; DD.raw_sorts = None }

let diamond (k:nat) : option DD.prepared =
  let d_nid = 100 in
  match run_ops (DD.with_budget DD.empty_cache ample ample) (diamond_ops k d_nid) with
  | Some c ->
    (match DD.prepare_certificate c [raw "refl" (d_nid + 3) []; raw "nnf-neg" (d_nid + 4) [0]] 1 0 with
     | DD.Built (_, p) -> Some p
     | _ -> None)
  | None -> None

let diamond_pending_by_default () : bool =
  match diamond 10 with
  | Some p ->
    (match own_conclusion p.DD.pcert with
     | Some j ->
       let c = p.DD.pcert in
       let n = U.count_cells 0 c.U.binder_entries in
       (match NR.judgments_of c.U.binder_entries I.Empty 0 with
        | Some cache ->
          (* the shared graph has k + 1 + 5 nodes besides sorts; the tree of D has 2^10 leaves *)
          CG.node_count p.DD.pgraph < 40 &&
          (* the default replay leaves it pending: its guard's work is spent on the names *)
          NR.replay [] c j = NR.Unreplayed &&
          not (U.binder_scoped c cache) &&
          (* with an unbounded work limit the same guard accepts it: the structure is fine *)
          U.binder_scoped_within (U.binder_demand_limit n) 1000000000000 c cache
        | None -> false)
     | None -> false)
  | None -> false

(* ---------------------------------------------------------------------- *)
(* A. The same certificate, pending by default, replayed by the DAG guard   *)
(*    (continued)                                                           *)
(* ---------------------------------------------------------------------- *)

let diamond_replayed_by_dag () : bool =
  match diamond 10 with
  | Some p ->
    (match own_conclusion p.DD.pcert with
     | Some j ->
       let r = dag [] p j in
       r.NRC.verdict = NR.Replayed && is_checked r &&
       (* the route of the document: the prepared certificate selects the DAG guard, the default stays pending *)
       (NRC.replay_route (NRC.DagV1 (DD.Ready p (0, 0))) [] p.DD.pcert j).NRC.verdict = NR.Replayed &&
       (NRC.replay_route NRC.Default [] p.DD.pcert j).NRC.verdict = NR.Unreplayed
     | None -> false)
  | None -> false

(* A wrong premise, a wrong target and a forward premise on the same diamond: not replayed. *)
let diamond_mutants () : bool =
  match diamond 10 with
  | Some p ->
    (match own_conclusion p.DD.pcert with
     | Some (U.Observational a b) ->
       let swapped = U.Observational b a in
       let r = dag [] p swapped in
       r.NRC.verdict = NR.Unreplayed && (match r.NRC.outcome with NRC.RootMismatch -> true | _ -> false) &&
       NR.replay [] p.DD.pcert swapped = NR.Unreplayed
     | _ -> false)
  | None -> false

(* The companion of another certificate: its graph and handles are those of the
   certificate it was prepared for; the conclusion of the other certificate is
   not the root of its own cache. *)
let other_companion () : bool =
  match diamond 3, diamond 4 with
  | Some p3, Some p4 ->
    (match own_conclusion p3.DD.pcert, own_conclusion p4.DD.pcert with
     | Some j3, Some j4 ->
       (dag [] p3 j3).NRC.verdict = NR.Replayed && (dag [] p4 j4).NRC.verdict = NR.Replayed &&
       (let r = dag [] p3 j4 in
        r.NRC.verdict = NR.Unreplayed && (match r.NRC.outcome with NRC.RootMismatch -> true | _ -> false))
     | _, _ -> false)
  | _, _ -> false

(* ---------------------------------------------------------------------- *)
(* B. Differential: small certificates                                      *)
(* ---------------------------------------------------------------------- *)

let pa : expr = App (symbol "p" [] bool_sort) []
let qa : expr = App (symbol "q" [] bool_sort) []
let twice (e:expr) : expr = neg (neg e)

let dn_entries : list U.binder_entry = [refl pa; be "nnf-neg" (oeq (twice pa) pa) [0]]

let nnf_cases () : bool =
  both [] dn_entries 1 NR.Replayed &&
  both_sorts [] dn_entries 1 NR.Replayed &&
  (* wrong target, wrong premise, missing premise *)
  both [] [refl pa; be "nnf-neg" (oeq (twice pa) qa) [0]] 1 NR.Unreplayed &&
  both [] [refl qa; be "nnf-neg" (oeq (twice pa) pa) [0]] 1 NR.Unreplayed &&
  both [] [refl pa; be "nnf-neg" (oeq (twice pa) pa) []] 1 NR.Unreplayed &&
  both_sorts [] [refl pa; be "nnf-neg" (oeq (twice pa) qa) [0]] 1 NR.Unreplayed &&
  (* a root that is not a consumed certificate *)
  both [] [refl pa] 0 NR.Unreplayed &&
  (* forward, self and negative premise ids: a rejected proof entry *)
  both [] [be "nnf-neg" (oeq (twice pa) pa) [1]; refl pa] 0 NR.Malformed &&
  both [] [refl pa; be "nnf-neg" (oeq (twice pa) pa) [1]] 1 NR.Malformed &&
  both [] [refl pa; be "nnf-neg" (oeq (twice pa) pa) [-1]] 1 NR.Malformed &&
  both_sorts [] [refl pa; be "nnf-neg" (oeq (twice pa) pa) [1]] 1 NR.Malformed &&
  (* a transitivity chain and a 3-ary De Morgan step *)
  both [] [refl pa; refl pa; be "trans" (oeq pa pa) [0; 1]; be "nnf-neg" (oeq (twice pa) pa) [2]] 3 NR.Replayed &&
  both [] [refl (neg pa);
           be "nnf-neg" (oeq (neg (mk_or [pa; pa; pa])) (mk_and [neg pa; neg pa; neg pa])) [0; 0; 0]] 1 NR.Replayed &&
  both [] [refl (neg pa);
           be "nnf-neg" (oeq (neg (mk_or [pa; pa; pa])) (mk_and [neg pa; neg pa; neg qa])) [0; 0; 0]] 1 NR.Unreplayed

(* The BreakVC shape (Z3QuantIntroReplayTests A1): implication to or under two
   nested Term binders; Var 1 is the outer binder under the inner one. *)
let pd : func_decl = symbol "P" [term] bool_sort
let qd : func_decl = symbol "Q" [term; term] bool_sort
let rd : func_decl = symbol "R" [term] bool_sort
let p_ (x:expr) : expr = App pd [x]
let q_ (x y:expr) : expr = App qd [x; y]
let r_ (x:expr) : expr = App rd [x]
let t0 : expr = Var 0 term
let t1 : expr = Var 1 term
let implies (a b:expr) : expr = App SP.implies_decl [a; b]
let in_l : expr = implies (q_ t1 t0) (r_ t0)
let in_r : expr = mk_or [neg (q_ t1 t0); r_ t0]
let all_l : expr = forall_ [term] in_l
let all_r : expr = forall_ [term] in_r
let out_l : expr = implies (p_ t0) all_l
let out_m : expr = implies (p_ t0) all_r
let out_r : expr = mk_or [neg (p_ t0); all_r]
let a1_lhs : expr = forall_ [term] out_l
let a1_rhs : expr = forall_ [term] out_r

let a1_entries : list U.binder_entry = [
  be "rewrite" (eqe in_l in_r) [];
  bq "quant-intro" [term] (eqe all_l all_r) [0];
  be "monotonicity" (eqe out_l out_m) [1];
  be "rewrite" (eqe out_m out_r) [];
  be "trans" (eqe out_l out_r) [2; 3];
  bq "quant-intro" [term] (eqe a1_lhs a1_rhs) [4]]

let quant_intro_cases () : bool =
  both [] a1_entries 5 NR.Replayed &&
  both_sorts [] a1_entries 5 NR.Replayed &&
  (* the same shape with the inner leaf's variable annotated at the outer sort: out of scope *)
  both [] [be "rewrite" (eqe in_l in_r) [];
           bq "quant-intro" [integer] (eqe all_l all_r) [0];
           be "monotonicity" (eqe out_l out_m) [1];
           be "rewrite" (eqe out_m out_r) [];
           be "trans" (eqe out_l out_r) [2; 3];
           bq "quant-intro" [term] (eqe a1_lhs a1_rhs) [4]] 5 NR.Unreplayed &&
  (* a missing congruence premise and a premise that is not an earlier entry *)
  both [] [be "rewrite" (eqe in_l in_r) [];
           bq "quant-intro" [term] (eqe all_l all_r) [];
           be "monotonicity" (eqe out_l out_m) [1];
           be "rewrite" (eqe out_m out_r) [];
           be "trans" (eqe out_l out_r) [2; 3];
           bq "quant-intro" [term] (eqe a1_lhs a1_rhs) [4]] 5 NR.Unreplayed &&
  both [] [be "rewrite" (eqe in_l in_r) [];
           bq "quant-intro" [term] (eqe all_l all_r) [0];
           be "monotonicity" (eqe out_l out_m) [1];
           be "rewrite" (eqe out_m out_r) [];
           be "trans" (eqe out_l out_r) [2; 3];
           bq "quant-intro" [term] (eqe a1_lhs a1_rhs) [6]] 5 NR.Malformed

(* ---------------------------------------------------------------------- *)
(* C. Wrong scopes                                                          *)
(* ---------------------------------------------------------------------- *)

let intro (bs:list sort) (b:expr) : list U.binder_entry =
  let q = forall_ bs b in
  [be "refl" (eqe b b) []; bq "quant-intro" bs (eqe q q) [0]]

let var (n:nat) (s:sort) : expr = Var n s
let real_s : sort = BaseSort "Real"
let arr (d:list sort) : sort = ArraySort d real_s
let named (s:string) : sort = BaseSort s

let scope_cases () : bool =
  let x = var 0 integer in
  let p0 = var 0 bool_sort in
  let nm1 = named "sort!1:T" in
  let nm2 = named "sort!2:T" in
  (* well-scoped: an open body under a binder, two binders read in reverse, a nested binder *)
  both [] (intro [integer] (eqe x x)) 1 NR.Replayed &&
  both [] (intro [nm1] (eqe (var 0 nm1) (var 0 nm1))) 1 NR.Replayed &&
  both [] (intro [arr [integer; bool_sort]] (eqe (var 0 (arr [integer; bool_sort])) (var 0 (arr [integer; bool_sort])))) 1
    NR.Replayed &&
  both [] (intro [integer; bool_sort] (eqe (eqe (var 1 integer) (var 1 integer)) p0)) 1 NR.Replayed &&
  both [] (intro [integer] (forall_ [bool_sort] (eqe (eqe (var 1 integer) (var 1 integer)) p0))) 1 NR.Replayed &&
  (* ill-scoped: another base sort, a name equal up to the native-id prefix, a domain order swap,
     the reversed binder order, a captured outer binder *)
  both [] (intro [integer] (eqe p0 p0)) 1 NR.Unreplayed &&
  both [] (intro [nm1] (eqe (var 0 nm2) (var 0 nm2))) 1 NR.Unreplayed &&
  both [] (intro [arr [integer; bool_sort]] (eqe (var 0 (arr [bool_sort; integer])) (var 0 (arr [bool_sort; integer])))) 1
    NR.Unreplayed &&
  both [] (intro [integer; bool_sort] (eqe (eqe (var 0 integer) (var 0 integer)) (var 1 bool_sort))) 1 NR.Unreplayed &&
  both [] (intro [integer] (forall_ [bool_sort] (eqe (eqe (var 0 integer) (var 0 integer)) p0))) 1 NR.Unreplayed &&
  (* the wrong scope is refused by the guard, with that outcome, not mistaken for exhaustion *)
  (match prepare (intro [integer] (eqe p0 p0)) 1 with
   | Some p ->
     (match own_conclusion p.DD.pcert with
      | Some j -> is_refused (dag [] p j)
      | None -> false)
   | None -> false)

(* ---------------------------------------------------------------------- *)
(* C. No fallback, and the budgets                                          *)
(* ---------------------------------------------------------------------- *)

let route_cases () : bool =
  let c = cert dn_entries 1 in
  match own_conclusion c with
  | Some j ->
    let unready (why:DD.unprepared_reason) : bool =
      let r = NRC.replay_route (NRC.DagV1 (DD.Unready why None)) [] c j in
      r.NRC.verdict = NR.Unreplayed && (match r.NRC.outcome with NRC.Unprepared _ -> true | _ -> false) in
    NR.replay [] c j = NR.Replayed &&
    (let d = NRC.replay_route NRC.Default [] c j in
     d.NRC.verdict = NR.Replayed && (match d.NRC.outcome with NRC.DefaultRoute -> true | _ -> false)) &&
    (* the default would replay this small certificate: a selected route that cannot run stays pending *)
    unready DD.UnpreparedClausal && unready DD.UnpreparedAbsent &&
    unready (DD.UnpreparedExhausted CT.Storage) && unready (DD.UnpreparedInvalid DD.MissingSort) &&
    (* the shape checks of the node's own certificate come first, as by default *)
    (let bad = cert [refl pa; be "nnf-neg" (oeq (twice pa) pa) [1]] 1 in
     match own_conclusion bad with
     | Some jb ->
       (NRC.replay_route (NRC.DagV1 (DD.Unready DD.UnpreparedClausal None)) [] bad jb).NRC.verdict = NR.Malformed &&
       (NRC.replay_route NRC.SortsV1 [] bad jb).NRC.verdict = NR.Malformed
     | None -> false) &&
    (let one = cert [refl pa] 0 in
     match own_conclusion one with
     | Some j1 ->
       (NRC.replay_route (NRC.DagV1 (DD.Unready DD.UnpreparedClausal None)) [] one j1).NRC.verdict = NR.Unreplayed &&
       (match (NRC.replay_route (NRC.DagV1 (DD.Unready DD.UnpreparedClausal None)) [] one j1).NRC.outcome with
        | NRC.NotConsumed -> true | _ -> false)
     | None -> false) &&
    (* the sorts route replays it too *)
    (NRC.replay_route NRC.SortsV1 [] c j).NRC.verdict = NR.Replayed
  | None -> false

let huge_budget : G.resource_budget = { G.preparation = ample; G.validation = ample; G.storage = ample }

let spent (b l:nat) : nat = if l <= b then b - l else 0

(* The exact units of the DAG guard on the BreakVC certificate, per phase: the guard
   checks at them and is exhausted in that phase one unit short, never refused. *)
let budget_cases () : bool =
  match prepare a1_entries 5 with
  | Some p ->
    (match own_conclusion p.DD.pcert with
     | Some j ->
       (match (NRC.replay_dag huge_budget [] p j).NRC.outcome with
        | NRC.GuardChecked left ->
          let pu = spent ample left.G.preparation in
          let vu = spent ample left.G.validation in
          let su = spent ample left.G.storage in
          let exact : G.resource_budget = { G.preparation = pu; G.validation = vu; G.storage = su } in
          pu > 0 && vu > 0 && su > 0 &&
          (NRC.replay_dag exact [] p j).NRC.verdict = NR.Replayed &&
          (let r = NRC.replay_dag ({ exact with G.preparation = pu - 1 }) [] p j in
           r.NRC.verdict = NR.Unreplayed && is_exhausted r CT.Preparation) &&
          (let r = NRC.replay_dag ({ exact with G.validation = vu - 1 }) [] p j in
           r.NRC.verdict = NR.Unreplayed && is_exhausted r CT.Validation) &&
          (let r = NRC.replay_dag ({ exact with G.storage = su - 1 }) [] p j in
           r.NRC.verdict = NR.Unreplayed && is_exhausted r CT.Storage)
        | _ -> false)
     | None -> false)
  | None -> false

(* ---------------------------------------------------------------------- *)
(* D. Open dependent Skolem steps                                           *)
(* ---------------------------------------------------------------------- *)

(* FStar.Nonempty query 2 node 92 (Z3NnfSkolemTests B1, transcribed): an nnf-pos
   root over forall [Universe; Term] of a Boolean equality whose right side is
   exists [Term]; the positive branch is the OPEN dependent step sk of
   @x2!1(#0:Term, #1:Universe), used at the scope [Term; Universe]. *)
let fuel : sort = BaseSort "Fuel"
let const (name:string) (s:sort) : expr = App (symbol name [] s) []
let iff (a b:expr) : expr = App (R.eq_decl bool_sort) [a; b]
let exists_ (bs:list sort) (b:expr) : expr = Quantifier Exists_k bs bool_sort b
let valid (x:expr) : expr = App (symbol "Valid" [term] bool_sort) [x]
let htf : func_decl = symbol "HasTypeFuel" [fuel; term; term] bool_sort
let max_ifuel : expr = const "MaxIFuel" fuel
let ht (f x t:expr) : expr = App htf [f; x; t]

let nonempty_d : func_decl = symbol "FStar.Nonempty.nonempty" [universe; term] term
let tag_d : func_decl = symbol "FStar.Nonempty.tag" [universe; term; term] term
let x2_1 : func_decl = symbol "@x2!1" [term; universe] term

let n_N : expr = valid (App nonempty_d [Var 1 universe; Var 0 term])
let n_body : expr = mk_and [ht max_ifuel (Var 0 term) (Var 1 term); valid (App tag_d [Var 2 universe; Var 1 term; Var 0 term])]
let n_B : expr = exists_ [term] n_body
let n_sk : expr = App x2_1 [Var 0 term; Var 1 universe]
let n_inst : expr = mk_and [ht max_ifuel n_sk (Var 0 term); valid (App tag_d [Var 1 universe; Var 0 term; n_sk])]
let n_fa : expr = forall_ [term] (neg n_body)
let n_tbody : expr = mk_and [mk_or [neg n_N; n_inst]; mk_or [n_N; n_fa]]
let n_src : expr = forall_ [universe; term] (iff n_N n_B)
let n_tgt : expr = forall_ [universe; term] n_tbody

let n92_entries : list U.binder_entry = [
  refl n_N;
  refl (neg n_N);
  be "sk" (oeq n_B n_inst) [];
  refl (neg n_body);
  bq "nnf-neg" [term] (oeq (neg n_B) n_fa) [3];
  be "nnf-pos" (oeq (iff n_N n_B) n_tbody) [0; 1; 2; 4];
  bq "nnf-pos" [universe; term] (oeq n_src n_tgt) [5]]

let n92_closure : expr = forall_ [universe; term] (iff n_B n_inst)

(* With the closure of the dependent step among the assertions the node is checked, by default
   and through the DAG guard (whose Skolem typing gate reads the open step at its scope id
   list); without it the step is not a choice equation and the node stays pending. *)
let open_skolem_cases () : bool =
  both [n92_closure] n92_entries 6 NR.Replayed &&
  both [] n92_entries 6 NR.Unreplayed &&
  both_sorts [n92_closure] n92_entries 6 NR.Replayed &&
  (match prepare n92_entries 6 with
   | Some p ->
     (match own_conclusion p.DD.pcert with
      | Some j -> is_checked (dag [n92_closure] p j)
      | None -> false)
   | None -> false)

(* The open step's scope ids reversed, outside the guard's contract: the loop's typing gate
   refuses the step at a scope where #0 is not a Term (the guard itself would refuse the scope:
   this isolates the gate). *)
let rec rev_each (ss:list (list nat)) : Tot (list (list nat)) (decreases ss) =
  match ss with
  | [] -> []
  | s :: rest -> L.rev s :: rev_each rest

let tampered_scope () : bool =
  match prepare n92_entries 6 with
  | Some p ->
    let c = p.DD.pcert in
    let n = U.count_cells 0 c.U.binder_entries in
    (match NR.judgments_of c.U.binder_entries I.Empty 0 with
     | Some cache ->
       (match DG.dag_guard (budget_of p) p.DD.pgraph c cache p.DD.phandles with
        | DG.DagChecked ds ->
          let gs = ds.DG.gs in
          let run (g:G.gstate) : NRC.steps_result =
            NRC.steps_ok_checked (NR.quant_intro_root c) [n92_closure] (U.count_cells 0 [n92_closure]) g cache
              I.Empty 0 c.U.binder_entries (U.binder_work_limit n) g.G.valid in
          let swapped : G.gstate =
            { gs with G.demands = I.index_put gs.G.demands 2 (rev_each (G.id_demanded gs.G.demands 2)) } in
          Cons? (G.id_demanded gs.G.demands 2) &&
          NRC.StepsOk? (run gs) &&
          NRC.StepsRejected? (run swapped) &&
          (* with no validation allowance left for the gate the loop is pending, not rejected *)
          NRC.StepsGateExhausted? (NRC.steps_ok_checked (NR.quant_intro_root c) [n92_closure]
                                     (U.count_cells 0 [n92_closure]) gs cache I.Empty 0 c.U.binder_entries
                                     (U.binder_work_limit n) 0)
        | _ -> false)
     | None -> false)
  | None -> false

(* The gate against the default on a checked sort table: reversed scopes, repeated sorts, array
   domains (order and arity), array ranges, nested arrays, short scopes, positions beyond the scope. *)
let s1 : sort = term
let s2 : sort = universe
let s3 : sort = integer
let s4 : sort = ArraySort [term; universe] integer
let s5 : sort = ArraySort [universe; term] integer
let s6 : sort = ArraySort [term] integer
let s7 : sort = ArraySort [term; universe] term
let s8 : sort = ArraySort [s4] integer
let s9 : sort = bool_sort
let s20 : sort = BaseSort native_name

let sort_of (x:int) : sort =
  if x = 1 then s1 else if x = 2 then s2 else if x = 3 then s3 else if x = 4 then s4
  else if x = 5 then s5 else if x = 6 then s6 else if x = 7 then s7 else if x = 8 then s8
  else if x = 9 then s9 else s20

let gate_raw : list CS.raw_sort = [
  CS.RawBase 1 "Term"; CS.RawBase 2 "Universe"; CS.RawBase 3 "Int"; CS.RawBase 9 "Bool";
  CS.RawBase 20 native_name;
  CS.RawArray 4 2 [1; 2] 3; CS.RawArray 5 2 [2; 1] 3; CS.RawArray 6 1 [1] 3; CS.RawArray 7 2 [1; 2] 1;
  CS.RawArray 8 1 [4] 3]

let table_budget : CS.sort_budget = { CS.preparation = ample; CS.storage = ample }

let rec sorts_of (xs:list int) : Tot (list sort) (decreases xs) =
  match xs with [] -> [] | x :: rest -> sort_of x :: sorts_of rest

let rec scopes_of (xss:list (list int)) : Tot (list (list sort)) (decreases xss) =
  match xss with [] -> [] | xs :: rest -> sorts_of xs :: scopes_of rest

let rec deps_of (ds:list (nat & int)) : Tot (list SK.dependency) (decreases ds) =
  match ds with [] -> [] | (n, x) :: rest -> (n, sort_of x) :: deps_of rest

let rec ids_of (g:CS.checked_sort_graph) (m:CS.id_map g) (xs:list int) : Tot (option (list nat)) (decreases xs) =
  match xs with
  | [] -> Some []
  | x :: rest ->
    (match CS.resolve_id g m x, ids_of g m rest with
     | Some i, Some is -> Some (i :: is)
     | _, _ -> None)

let rec scope_ids_of (g:CS.checked_sort_graph) (m:CS.id_map g) (xss:list (list int))
  : Tot (option (list (list nat))) (decreases xss) =
  match xss with
  | [] -> Some []
  | xs :: rest ->
    (match ids_of g m xs, scope_ids_of g m rest with
     | Some is, Some iss -> Some (is :: iss)
     | _, _ -> None)

(* The gate decides `expected` on the ids, which is what the default gate decides on the sorts. *)
let gate_is (expected:bool) (deps:list (nat & int)) (scopes:list (list int)) : bool =
  match CS.validate_checked_sort_graph gate_raw table_budget with
  | CS.Prepared g m _ ->
    (match scope_ids_of g m scopes with
     | Some sc ->
       (match NRC.scopes_typed_ids g sc (deps_of deps) ample with
        | Some (b, _) -> b = expected && NR.all_typed (scopes_of scopes) (deps_of deps) = expected
        | None -> false)
     | None -> false)
  | _ -> false

let gate_cases () : bool =
  let d_tu = [(0, 1); (1, 2)] in
  (* the n92 dependencies at [Term; Universe], at a scope with Int at #1, reversed, one short, and two scopes *)
  gate_is true d_tu [[1; 2]] &&
  gate_is false d_tu [[1; 3]] &&
  gate_is false d_tu [[2; 1]] &&
  gate_is false d_tu [[1]] &&
  gate_is true d_tu [[1; 2]; [1; 2; 3]] &&
  gate_is false d_tu [[1; 2]; [1; 3]] &&
  gate_is true d_tu [] &&
  gate_is true [] [[3]; []] &&
  (* a position beyond the scope, and a position past a longer scope *)
  gate_is false [(5, 1)] [[1; 1; 1]] &&
  gate_is true [(2, 1)] [[2; 3; 1]] &&
  (* repeated sorts *)
  gate_is true [(0, 1); (1, 1); (2, 1)] [[1; 1; 1]] &&
  gate_is false [(0, 1); (1, 1); (2, 1)] [[1; 1; 3]] &&
  (* array domains: order, arity, range; nested arrays *)
  gate_is true [(0, 4)] [[4]] &&
  gate_is false [(0, 4)] [[5]] &&
  gate_is false [(0, 4)] [[6]] &&
  gate_is false [(0, 4)] [[7]] &&
  gate_is false [(0, 4)] [[3]] &&
  gate_is true [(0, 8); (1, 5)] [[8; 5]] &&
  gate_is false [(0, 8); (1, 5)] [[8; 4]] &&
  gate_is true [(1, 20)] [[3; 20]] &&
  gate_is false [(1, 20)] [[3; 1]] &&
  gate_is false [(0, 9)] [[3]] &&
  gate_is true [(0, 9)] [[9; 9]]

(* The gate's units are charged: the exact allowance succeeds, one short is exhaustion
   (neither a pass nor a refusal); a name longer than the allowance is exhaustion at its
   counter, never a long scan. *)
let used_units (b l:nat) : nat = spent b l

let gate_units () : bool =
  match CS.validate_checked_sort_graph gate_raw table_budget with
  | CS.Prepared g m _ ->
    (match scope_ids_of g m [[1; 2; 3]; [1; 2]] with
     | Some sc ->
       let deps = deps_of [(0, 1); (1, 2)] in
       (match NRC.scopes_typed_ids g sc deps ample with
        | Some (true, left) ->
          let u = used_units ample left in
          u > 0 &&
          (match NRC.scopes_typed_ids g sc deps u with Some (true, 0) -> true | _ -> false) &&
          (match NRC.scopes_typed_ids g sc deps (u - 1) with None -> true | _ -> false)
        | _ -> false) &&
       (match CS.resolve_id g m 20 with
        | Some id20 ->
          (match NRC.sort_matches g (NRC.match_cost + 20) [NRC.MPair id20 s20] with
           | Some (true, 0) -> true | _ -> false) &&
          (match NRC.sort_matches g (NRC.match_cost + 19) [NRC.MPair id20 s20] with None -> true | _ -> false) &&
          (match NRC.sort_matches g (NRC.match_cost + 5) [NRC.MPair id20 (BaseSort "Term")] with
           | Some (false, _) -> true | _ -> false) &&
          (match NRC.sort_matches g 33 [NRC.MPair id20 s20] with None -> true | _ -> false)
        | None -> false)
     | None -> false)
  | _ -> false

(* A sort 50,000 arrays deep matched against its id: a worklist, not a stack. *)
let rec domain_nested (depth:nat) (acc:sort) : Tot sort (decreases depth) =
  if depth = 0 then acc else domain_nested (depth - 1) (ArraySort [acc] integer)

let rec deep_raw (i d:nat) (acc:list CS.raw_sort) : Tot (list CS.raw_sort) (decreases d - i) =
  if i >= d then L.rev acc else deep_raw (i + 1) d (CS.RawArray (i + 2) 1 [i + 1] 1 :: acc)

let deep_sorts () : bool =
  let d = 50000 in
  match CS.validate_checked_sort_graph (deep_raw 0 d [CS.RawBase 1 "Int"]) table_budget with
  | CS.Prepared g m _ ->
    (match CS.resolve_id g m (d + 1) with
     | Some top ->
       (match NRC.sort_matches g ample [NRC.MPair top (domain_nested d integer)],
              NRC.sort_matches g ample [NRC.MPair top (domain_nested d (BaseSort "Bool"))],
              NRC.sort_matches g ample [NRC.MPair top (domain_nested (d - 1) integer)] with
        | Some (true, _), Some (false, _), Some (false, _) -> true
        | _, _, _ -> false)
     | None -> false)
  | _ -> false

(* ---------------------------------------------------------------------- *)
(* Run                                                                      *)
(* ---------------------------------------------------------------------- *)

let run () : bool =
  diamond_pending_by_default () && diamond_replayed_by_dag () && diamond_mutants () && other_companion () &&
  nnf_cases () && quant_intro_cases () && scope_cases () && route_cases () && budget_cases () &&
  open_skolem_cases () && tampered_scope () && gate_cases () && gate_units () && deep_sorts ()
