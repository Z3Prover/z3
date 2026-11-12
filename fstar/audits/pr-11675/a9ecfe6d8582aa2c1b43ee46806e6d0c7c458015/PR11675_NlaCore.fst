module PR11675_NlaCore
(* Abstract model of the two behavioral changes in nla_core.cpp (PR 11675).
   Not a proof of the C++ execution. *)
type lbool = | L_true | L_false | L_undef

(* check_monic: head version; relevance guard now active.
   relevant = is_relevant(m.var()) (true when m_relevant unset);
   int_nonint = column_is_int && value not integral; prod_eq = product == value *)
let check_monic_new (relevant int_nonint prod_eq: bool) : bool =
  if not relevant then true
  else if int_nonint then true
  else prod_eq

let check_monic_old (relevant int_nonint prod_eq: bool) : bool =
  if int_nonint then true else prod_eq

(* O1: irrelevant monics are never reported inconsistent *)
let o1 (i p: bool) : Lemma (check_monic_new false i p = true) = ()

(* O2: for relevant monics behavior is unchanged; the new check only weakens
   (accepts a superset of) the old one, so it can only drop refinement work. *)
let o2 (r i p: bool) : Lemma
  (ensures (r ==> check_monic_new r i p = check_monic_old r i p) /\
           (check_monic_old r i p ==> check_monic_new r i p)) = ()

(* Final fallback. nlsat_unbounded is the result of the old unbounded call;
   the bounded call either finishes with the same answer or exhausts budget
   (assumption A: budget exhaustion only produces l_undef, i.e. nlsat's
   conflict/rlimit cutoffs never fabricate l_true/l_false). *)
let bounded (unb: lbool) (exhausted: bool) : lbool =
  if exhausted then L_undef else unb

(* O3: new final result is either the old result or l_undef (sound, maybe
   incomplete); and l_undef is produced only when the budget is exhausted. *)
let o3 (unb: lbool) (ex: bool) : Lemma
  (ensures (bounded unb ex = unb \/ bounded unb ex = L_undef) /\
           (bounded unb ex = L_undef /\ unb <> L_undef ==> ex)) = ()

(* Witness of the completeness cost: a reachable-in-model case where old
   returned a definite answer and new returns l_undef. *)
let incompleteness_witness () : Lemma (bounded L_true true = L_undef /\ bounded L_true true <> L_true) = ()
