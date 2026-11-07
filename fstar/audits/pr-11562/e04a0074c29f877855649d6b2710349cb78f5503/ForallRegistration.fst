module ForallRegistration
(* Abstract model of head e04a0074 smt_internalizer.cpp lines 655-676 (forall registration)
   and undo_mk_bool_var lines 1106-1122. Polarity: l_false=-1, l_undef=0, l_true=1. *)
open FStar.List.Tot

type pol = | PFalse | PUndef | PTrue

(* manager: m_quantifiers vector (ids); bvars: ids with a bool var, in creation order (m_b_internalized_stack, head = most recent) *)
type st = { mgr: list nat; bvars: list nat }

let internalize_forall (q:nat) (p:pol) (s:st) : st =
  if mem q s.bvars then s   (* b_internalized(q): skip the whole add block *)
  else { bvars = q :: s.bvars;
         mgr = (if p <> PFalse then s.mgr @ [q] else s.mgr) }

(* undo_mk_bool_var: del for every forall, m_quantifiers.pop_back() *)
let undo (s:st) : st =
  match s.bvars with
  | [] -> s
  | _ :: bs -> { bvars = bs; mgr = (match rev s.mgr with [] -> [] | _ :: r -> rev r) }

let empty : st = { mgr = []; bvars = [] }

(* Witness 1: Q first seen negatively (e.g. clause (or (not Q) c)), later positively
   (e.g. clause (or Q b)): Q has a bool var, was seen with polarity l_true, but is never registered. *)
let w1 = internalize_forall 1 PTrue (internalize_forall 1 PFalse empty)
let _ = assert_norm (mem 1 w1.bvars /\ ~(mem 1 w1.mgr))

(* Witness 2: Q1 registered; Q2 only negative (no add); undoing Q2's bool var pops Q1's registration. *)
let w2 = undo (internalize_forall 2 PFalse (internalize_forall 1 PTrue empty))
let _ = assert_norm (w2.mgr == [] /\ w2.bvars == [1])   (* Q1 still internalized but unregistered *)

(* Witness 3: undo of a negative-only forall on empty manager pops an empty vector *)
let w3_pre = internalize_forall 1 PFalse empty
let _ = assert_norm (w3_pre.mgr == [] /\ w3_pre.bvars == [1])

(* Control: with only positive/undef polarities the model is balanced *)
let ok = undo (internalize_forall 1 PTrue empty)
let _ = assert_norm (ok == empty)
