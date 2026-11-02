(*
   Z3CheckedGuardTests.fst

   Executable tests of the opt-in guard (`Z3CheckedGuard.verified_guard`),
   run natively by the Cherry checker tests (`Z3CherryTests.run`) and
   verified with the F* test modules. Each case is a binder certificate with
   the cache of its entries' judgments, checked with explicit budgets:

   * well-scoped certificates are `Checked`: an open body under one binder,
     two binders read in reverse (`Var 0` the last), a nested binder that
     shadows, a premise shared under two scopes (a DAG);
   * ill-scoped ones are `Refused`: a variable whose annotation is not its
     binder's sort (a different base sort, a name equal up to its native-id
     prefix, an array sort with its domain reordered, a captured outer
     binder), an ill-scoped entry inside, a premise that is not an earlier
     entry, an open root;
   * at each budget's exact units of a checked case the guard checks, and one
     unit short it is `Exhausted` in that phase, never `Refused`.
*)
module Z3CheckedGuardTests

module A = Z3AstTheory
module R = Z3ResolutionProofTheory
module U = Z3UnifiedProof
module G = Z3CheckedGuard
module T = Z3CheckedTerms
module I = Z3ProofIndex

let int_s : A.sort = A.BaseSort "Int"
let real_s : A.sort = A.BaseSort "Real"

let entry (name:string) (formula:A.expr) (premises:list int) (sorts:option (list A.sort)) : U.binder_entry =
  { U.binder_name = name; U.binder_formula = formula; U.binder_premises = premises; U.binder_sorts = sorts }

let all (bs:list A.sort) (b:A.expr) : A.expr = A.Quantifier A.Forall_k bs A.bool_sort b

let eqe (a b:A.expr) : A.expr = R.mk_eq_expr a b

let var (n:nat) (s:A.sort) : A.expr = A.Var n s

(* The judgments of the entries, by index, as the checker's cache holds them. *)
let rec cache_of (entries:list U.binder_entry) (cache:I.index_tree U.judgment) (k:nat)
  : Tot (option (I.index_tree U.judgment)) (decreases entries) =
  match entries with
  | [] -> Some cache
  | e :: rest ->
    (match U.classify_fact e.U.binder_formula with
     | Some j -> cache_of rest (I.index_put cache k j) (k + 1)
     | None -> None)

let big : G.resource_budget = { G.preparation = 1000000; G.validation = 1000000; G.storage = 1000000 }

let run_guard (budget:G.resource_budget) (entries:list U.binder_entry) (root:int) : option G.guard_result =
  match cache_of entries I.Empty 0 with
  | Some cache -> Some (G.verified_guard budget ({ U.binder_entries = entries; U.binder_root = root }) cache)
  | None -> None

let checked (entries:list U.binder_entry) (root:int) : bool =
  match run_guard big entries root with Some (G.Checked _) -> true | _ -> false

let refused (entries:list U.binder_entry) (root:int) : bool =
  match run_guard big entries root with Some (G.Refused _) -> true | _ -> false

(* An open body `b` (with its closed counterpart `q`) under the binder sorts `bs`. *)
let intro (bs:list A.sort) (b:A.expr) : list U.binder_entry =
  let q = all bs b in
  [entry "refl" (eqe b b) [] None; entry "quant-intro" (eqe q q) [0] (Some bs)]

let scoped_cases () : bool =
  let x = var 0 int_s in
  let p0 = var 0 A.bool_sort in
  let named (s:string) : A.sort = A.BaseSort s in
  let arr (d:list A.sort) : A.sort = A.ArraySort d real_s in
  (* open bodies under binders *)
  checked (intro [int_s] (eqe x x)) 1 &&
  refused (intro [int_s] (eqe p0 p0)) 1 &&
  checked (intro [named "sort!1:T"] (eqe (var 0 (named "sort!1:T")) (var 0 (named "sort!1:T")))) 1 &&
  refused (intro [named "sort!1:T"] (eqe (var 0 (named "sort!2:T")) (var 0 (named "sort!2:T")))) 1 &&
  checked (intro [arr [int_s; A.bool_sort]] (eqe (var 0 (arr [int_s; A.bool_sort])) (var 0 (arr [int_s; A.bool_sort])))) 1 &&
  refused (intro [arr [int_s; A.bool_sort]] (eqe (var 0 (arr [A.bool_sort; int_s])) (var 0 (arr [A.bool_sort; int_s])))) 1 &&
  (* two binders, `Var 0` the last: [Int; Bool] reads Var 0 : Bool, Var 1 : Int *)
  checked (intro [int_s; A.bool_sort] (eqe (eqe (var 1 int_s) (var 1 int_s)) p0)) 1 &&
  refused (intro [int_s; A.bool_sort] (eqe (eqe (var 0 int_s) (var 0 int_s)) (var 1 A.bool_sort))) 1 &&
  (* a nested binder shadows: under forall y:Bool, Var 0 is y and Var 1 is x *)
  checked (intro [int_s] (all [A.bool_sort] (eqe (eqe (var 1 int_s) (var 1 int_s)) p0))) 1 &&
  refused (intro [int_s] (all [A.bool_sort] (eqe (eqe (var 0 int_s) (var 0 int_s)) p0))) 1

let refusal_cases () : bool =
  let x = var 0 int_s in
  let p0 = var 0 A.bool_sort in
  let tt = R.true_expr in
  let ok = all [int_s] (eqe x x) in
  let top = all [int_s] tt in
  (* an ill-scoped entry inside a well-scoped root *)
  refused [entry "rewrite" (eqe p0 tt) [] None; entry "quant-intro" (eqe ok top) [0] (Some [int_s])] 1 &&
  (* a premise that is not an earlier entry *)
  refused [entry "quant-intro" (eqe ok ok) [1] (Some [int_s]); entry "refl" (eqe (eqe x x) (eqe x x)) [] None] 0 &&
  refused [entry "refl" (eqe tt tt) [] None; entry "quant-intro" (eqe ok ok) [1] (Some [int_s])] 1 &&
  (* an open root *)
  refused [entry "refl" (eqe x x) [] None] 0 &&
  (* a root that is not an entry *)
  refused (intro [int_s] (eqe x x)) 2 &&
  refused (intro [int_s] (eqe x x)) (-1)

(* A premise shared under an Int and a Bool binder: a closed premise is
   checked at both scopes; an open one fits only one of them. *)
let shared_cases () : bool =
  let tt = R.true_expr in
  let x = var 0 int_s in
  let closed = entry "refl" (eqe tt tt) [] None in
  let opened = entry "refl" (eqe (eqe x x) (eqe x x)) [] None in
  let q (s:A.sort) (p:int) = entry "quant-intro" (eqe (all [s] tt) (all [s] tt)) [p] (Some [s]) in
  let join = entry "monotonicity" (eqe tt tt) [1; 2] None in
  checked [closed; q int_s 0; q A.bool_sort 0; join] 3 &&
  refused [opened; q int_s 0; q A.bool_sort 0; join] 3

let outcome_code (r:option G.guard_result) : int =
  match r with
  | Some (G.Checked _) -> 0
  | Some (G.Refused _) -> 1
  | Some (G.Exhausted T.Preparation) -> 2
  | Some (G.Exhausted T.Validation) -> 3
  | Some (G.Exhausted T.Storage) -> 4
  | None -> 5

(* The exact units of each budget, and one short. The units are pinned: 4,621 preparation, 1,545
   validation and 1,622 storage (the same on both backends, test_native_bridge.ml). *)
let boundary_cases () : bool =
  let x = var 0 int_s in
  let entries = intro [int_s; A.bool_sort] (all [int_s] (eqe (eqe x x) (eqe (var 1 A.bool_sort) (var 1 A.bool_sort)))) in
  match run_guard big entries 1 with
  | Some (G.Checked st) ->
    st.G.prep < big.G.preparation && st.G.valid < big.G.validation && st.G.store < big.G.storage &&
    (let p : nat = big.G.preparation - st.G.prep in
     let v : nat = big.G.validation - st.G.valid in
     let s : nat = big.G.storage - st.G.store in
    p = 4621 && v = 1545 && s = 1622 &&
    outcome_code (run_guard ({ big with G.preparation = p }) entries 1) = 0 &&
    outcome_code (run_guard ({ big with G.preparation = p - 1 }) entries 1) = 2 &&
    outcome_code (run_guard ({ big with G.validation = v }) entries 1) = 0 &&
    outcome_code (run_guard ({ big with G.validation = v - 1 }) entries 1) = 3 &&
    outcome_code (run_guard ({ big with G.storage = s }) entries 1) = 0 &&
    outcome_code (run_guard ({ big with G.storage = s - 1 }) entries 1) = 4 &&
    outcome_code (run_guard ({ G.preparation = p; G.validation = v; G.storage = s }) entries 1) = 0)
  | _ -> false

(* A 1000-character sort name is checked; an 8 MiB one exhausts preparation
   under the mode's own budget, at the node, which stays pending. *)
let long_name_cases () : bool =
  let pending (s:A.sort) : int =
    let x = var 0 s in
    let q = all [s] (eqe x x) in
    let node = { U.kind = U.QuantifierIntroduction ({ U.binder_entries = intro [s] (eqe x x); U.binder_root = 1 });
                 U.conclusion = U.Equal q q; U.premises = [] } in
    match fst (G.check_node_verified [] true [] (fun _ -> false) node) with
    | Some (_, n) -> n
    | None -> -1 in
  pending (A.BaseSort (FStar.String.make 1000 'S')) = 0 &&
  pending (A.BaseSort (FStar.String.make 8388608 'S')) = 1

let run () : bool =
  scoped_cases () && refusal_cases () && shared_cases () && boundary_cases () && long_name_cases ()
