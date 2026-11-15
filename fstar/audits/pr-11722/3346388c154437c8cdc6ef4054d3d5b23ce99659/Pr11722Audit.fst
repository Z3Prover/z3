module Pr11722Audit
open FStar.List.Tot

(* Abstract model: a candidate model is (x, b); base assertion is b ==> x = 0;
   the assumption literal is b. *)
type model = { x: int; b: bool }
let base (m:model) : bool = (not m.b) || m.x = 0

let rec max_of (l: list model) (best: option int) : option int =
  match l with
  | [] -> best
  | m :: tl -> max_of tl (match best with None -> Some m.x | Some v -> Some (if m.x > v then m.x else v))

(* Scope asserts base and the assumptions; the recheck is satisfiable iff some candidate survives. *)
let scope_new (cands: list model) : list model = filter (fun m -> base m && m.b) cands
let scope_old (cands: list model) : list model = filter base cands

(* PR: unsat recheck => return false (None); else maximize over surviving models *)
let isolated_new (cands: list model) : option int =
  match scope_new cands with [] -> None | l -> max_of l None

(* O1: every model considered by the new scope satisfies the assumption and base *)
let o1 (cands: list model) (m: model) : Lemma (requires memP m (scope_new cands)) (ensures m.b = true /\ m.x = 0) =
  mem_filter (fun m -> base m && m.b) cands m

(* O2: refutation witness for the old behaviour: a model violating the assumption is admitted
   by old scope with a larger objective, new scope excludes it. *)
let w1 : model = { x = 5; b = false }
let w2 : model = { x = 0; b = true }
let o2 () : Lemma (ensures
    memP w1 (scope_old [w1; w2]) /\ ~(memP w1 (scope_new [w1; w2])) /\
    max_of (scope_old [w1; w2]) None == Some 5 /\ isolated_new [w1; w2] == Some 0) =
  assert_norm (max_of (scope_old [w1; w2]) None == Some 5);
  assert_norm (isolated_new [w1; w2] == Some 0);
  assert_norm (memP w1 (scope_old [w1; w2]));
  assert_norm (~(memP w1 (scope_new [w1; w2])))

(* O3: update_lower failure handling in geometric_opt. Old: failure returned `true`
   (treated as a valid unbounded step, is_sat stays l_true). New: failure => l_undef + break. *)
type lb = | Sat | Undef
let update_lower_old (ok: bool) : bool (*has_bound-input true? returns bound_is_true*) = if ok then false else true
let step_new (ok: bool) : lb = if ok then Sat else Undef
let o3 (ok: bool) : Lemma (ensures (not ok ==> step_new ok = Undef) /\ (ok ==> step_new ok = Sat)) = ()
let o3_old_differs () : Lemma (update_lower_old false = true /\ step_new false = Undef) = ()
