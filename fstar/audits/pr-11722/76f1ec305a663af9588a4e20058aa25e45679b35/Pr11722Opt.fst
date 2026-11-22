module Pr11722Opt
(* Abstract model of PR 11722 (opt_solver::maximize_objective_isolated and
   optsmt::geometric_opt).  A model is (x, b): objective value and one
   assumption literal.  Base assertion is (b ==> x = 0) as in the PR test. *)
open FStar.List.Tot

type model = { x: int; b: bool }

let base (m:model) : bool = (not m.b) || m.x = 0
let assum (m:model) : bool = m.b          (* the assumption literal *)

(* candidate models explored by the solver, finite abstraction *)
let rec max_of (l: list model) (best: option int) : option int =
  match l with
  | [] -> best
  | m :: tl ->
    let best' = (match best with None -> Some m.x | Some v -> Some (if m.x > v then m.x else v)) in
    max_of tl best'

let rec filter_models (p: model -> bool) (l: list model) : list model =
  match l with [] -> [] | m::tl -> if p m then m :: filter_models p tl else filter_models p tl

(* PR behaviour: scope asserts base AND assumptions; recheck; None = return false *)
let isolated_new (cands: list model) : option int =
  max_of (filter_models (fun m -> base m && assum m) cands) None

(* Old behaviour: assumptions not asserted in the scope *)
let isolated_old (cands: list model) : option int =
  max_of (filter_models base cands) None

(* O1 (counterexample to old code): a reachable witness where assumption b is
   true in the sat model, but old scope sees a model with b=false, x=5, so the
   old result exceeds the true optimum 0 under the assumption. *)
let witness : list model = [ {x=0; b=true}; {x=5; b=false} ]
let o1_old_overshoots () : Lemma (isolated_old witness == Some 5 /\ isolated_new witness == Some 0) = ()

(* O2: the new result dominates every model satisfying base and the assumption (no overshoot below the true optimum). *)
let rec max_of_ub (l: list model) (best: option int) (v:int) (m0: model)
  : Lemma (requires max_of l best == Some v /\ memP m0 l)
          (ensures m0.x <= v) (decreases l) =
  match l with
  | [] -> ()
  | m :: tl ->
    let best' = (match best with None -> Some m.x | Some w -> Some (if m.x > w then m.x else w)) in
    if m0 == m then (
      let rec mono (l2: list model) (b: int) : Lemma (ensures (match max_of l2 (Some b) with Some r -> r >= b | None -> false)) (decreases l2) =
        (match l2 with [] -> () | h::t -> mono t (if h.x > b then h.x else b)) in
      match best' with Some b -> mono tl b | None -> ())
    else max_of_ub tl best' v m0

let rec filter_mem (p: model -> bool) (l: list model) (m: model)
  : Lemma (ensures memP m (filter_models p l) <==> (memP m l /\ p m)) (decreases l) =
  match l with [] -> () | h::t -> filter_mem p t m

let o2_sound_ub (cands: list model) (v:int) (m0: model)
  : Lemma (requires isolated_new cands == Some v /\ memP m0 cands /\ base m0 /\ assum m0)
          (ensures m0.x <= v) =
  filter_mem (fun m -> base m && assum m) cands m0;
  max_of_ub (filter_models (fun m -> base m && assum m) cands) None v m0

(* O3: failed recheck/update_lower propagates l_undef: never a bound of true / unbounded. *)
type lbool = | L_true | L_false | L_undef
let geometric_step (upd_ok: bool) : lbool = if upd_ok then L_true else L_undef
let o3_failure_is_undef () : Lemma (geometric_step false == L_undef) = ()
let isolated_status (cands: list model) : bool = Some? (isolated_new cands)
let o3_empty_returns_false () : Lemma (isolated_status [] == false) = ()
