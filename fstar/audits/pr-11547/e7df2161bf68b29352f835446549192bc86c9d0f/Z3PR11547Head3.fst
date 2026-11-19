module Z3PR11547Head3
(* Control-flow model of PR 11547 head e7df2161: three changed behaviours. *)

(* O1: smt_tactic l_false branch. pr_opt: None = null proof; Some f = proof whose fact is f.
   Mirrors: if proofs_enabled && (!pr || !is_false(get_fact(pr))) throw. *)
type fact = | FFalse | FOther
type outcome = | Throw | AssertFalse of option fact

let smt_unsat (proofs:bool) (pr:option fact) : outcome =
  if proofs && (None? pr || pr <> Some FFalse) then Throw
  else AssertFalse pr

(* with proofs on, asserting false never happens without a proof whose fact is false *)
let o1 (pr:option fact)
  : Lemma (match smt_unsat true pr with
           | Throw -> True
           | AssertFalse p -> p == Some FFalse) = ()

(* proofs off: unchanged behaviour (asserts false) *)
let o1b (pr:option fact) : Lemma (AssertFalse? (smt_unsat false pr)) = ()

(* O2: then_simplifier::reduce. A step is either supported or not; unsupported steps
   are skipped under proofs. Executed steps list must all support proofs. *)
type step = { supports:bool }

let rec executed (proofs:bool) (l:list step) : list step =
  match l with
  | [] -> []
  | s :: tl -> if proofs && not s.supports then executed proofs tl else s :: executed proofs tl

let rec all_supp (l:list step) : bool =
  match l with [] -> true | s :: tl -> s.supports && all_supp tl

let rec o2 (l:list step) : Lemma (ensures all_supp (executed true l)) =
  match l with [] -> () | _ :: tl -> o2 tl

let rec o2b (l:list step) : Lemma (ensures executed false l == l) =
  match l with [] -> () | _ :: tl -> o2b tl

(* O3: no-op guards (horn, nlqsat, ctx_solver_simplify, add_bounds): with proofs the
   goal is returned unchanged; without proofs the implementation runs. *)
type goal = { fmls:list int; pf:bool }
let guarded (impl:goal -> goal) (g:goal) : goal = if g.pf then g else impl g

let o3 (impl:goal -> goal) (g:goal)
  : Lemma (requires g.pf) (ensures guarded impl g == g) = ()
let o3b (impl:goal -> goal) (g:goal)
  : Lemma (requires not g.pf) (ensures guarded impl g == impl g) = ()
