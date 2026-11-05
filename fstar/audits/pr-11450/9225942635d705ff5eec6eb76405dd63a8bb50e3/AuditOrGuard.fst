module AuditOrGuard

(* Self-contained model of func_decl; sorts are abstract ids, bool_sort = 0. *)
type decl = { decl_name:string; domain:list int; range:int; interp:option int; int_params:list int }

let bool_sort : int = 0
let op_or : int = 5

let rec boolean_sorts (d:list int) : Tot bool (decreases d) =
  match d with [] -> true | s :: r -> s = bool_sort && boolean_sorts r

(* PR's canonical_or *)
let canonical_or (f:decl) : bool =
  f.decl_name = "or" && f.interp = Some op_or && boolean_sorts f.domain &&
  f.range = bool_sort && f.int_params = []

(* Z3IntegerDivision.check guard before and after the PR *)
let old_guard (f:decl) : bool =
  f.decl_name = "or" && f.interp = Some op_or && f.domain = [bool_sort; bool_sort] && f.range = bool_sort
let new_guard (f:decl) : bool =
  canonical_or f && f.domain = [bool_sort; bool_sort] && f.range = bool_sort

(* O1: the new guard never accepts a declaration the old one rejected. *)
let o1 (f:decl) : Lemma (requires new_guard f) (ensures old_guard f) = ()

(* O2: the only inputs newly rejected carry integer parameters. *)
let o2 (f:decl) : Lemma (requires old_guard f /\ not (new_guard f)) (ensures f.int_params <> []) = ()

(* O3: a witness for O2 exists, so the tightening is real; and a clashing tag is rejected. *)
let w : decl = { decl_name="or"; domain=[0;0]; range=0; interp=Some op_or; int_params=[7] }
let o3 () : Lemma (old_guard w /\ not (new_guard w) /\ not (canonical_or {w with int_params=[]; interp=Some 114})) = ()
