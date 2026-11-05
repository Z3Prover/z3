module SatCoreLevel0
(* Model of the m_core filter in sat::solver::resolve_conflict_for_unsat_core
   (PR 11474, sat_solver.cpp:2828-2837). An entry carries lvl(lit) and whether
   value(lit)==l_false; core literals are assigned (not l_undef). *)
type entry = { id: nat; lvl: nat; is_false: bool }

let new_keep (e:entry) : bool = e.lvl > 0 || e.is_false
let old_keep (e:entry) : bool = e.lvl > 0

let rec filter (f: entry -> bool) (l: list entry) : list entry =
  match l with [] -> [] | h::t -> if f h then h :: filter f t else filter f t

(* Level-0 assigned literals are implied by the clauses: a level-0 literal that
   is not false is true in every model of F. [entailed] is that environment fact. *)
let entailed (e:entry) : prop = (e.lvl = 0 /\ not e.is_false)

(* O1: every literal dropped by the new filter is entailed by F (so dropping is sound). *)
let rec o1 (l: list entry) : Lemma
  (ensures forall e. FStar.List.Tot.memP e l /\ not (new_keep e) ==> entailed e) =
  match l with [] -> () | _::t -> o1 t

(* O2: every literal false at level 0 (contradicting F) is retained. *)
let rec o2 (l: list entry) : Lemma
  (ensures forall e. FStar.List.Tot.memP e l /\ e.lvl = 0 /\ e.is_false ==> FStar.List.Tot.memP e (filter new_keep l)) =
  match l with [] -> () | _::t -> o2 t

(* O3: new filter is a subset-preserving refinement of old: it retains everything old retained. *)
let rec o3 (l: list entry) : Lemma
  (ensures forall e. FStar.List.Tot.memP e (filter old_keep l) ==> FStar.List.Tot.memP e (filter new_keep l)) =
  match l with [] -> () | _::t -> o3 t

(* Counterexample for the OLD filter: a level-0-false assumption is dropped. *)
let a : entry = { id = 0; lvl = 0; is_false = true }
let b : entry = { id = 1; lvl = 1; is_false = false }
let old_cex () : Lemma
  (ensures filter old_keep [a; b] == [b] /\ filter new_keep [a; b] == [a; b]) = ()
