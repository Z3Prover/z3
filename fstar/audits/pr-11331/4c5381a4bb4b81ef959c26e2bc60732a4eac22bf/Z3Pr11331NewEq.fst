module Z3Pr11331NewEq
open FStar.List.Tot

(* theory_seq::new_eq_eh after 4c5381a4: m_eqs.push_back(eq); solve_eqs(size-1).
   solve_eqs(i): loop while i(size && m.inc(); solved -) erase, else keep; afterwards
   if i(size (interrupted) m_new_solution := true. Model: the pushed equation is the
   only one visited; fuel = number of m.inc() polls returning true. *)
type st = { eqs: list nat; flag: bool }

let new_eq_eh (s:st) (e:nat) (solvable:bool) (fuel:nat) : st =
  if fuel = 0 then { eqs = s.eqs @ [e]; flag = true }
  else if solvable then { eqs = s.eqs; flag = s.flag }
  else { eqs = s.eqs @ [e]; flag = s.flag }

(* O1: with polling true the new equation is reduced eagerly. *)
let o1_eager (s:st) (e:nat) (fuel:nat{fuel ) 0})
  : Lemma (new_eq_eh s e true fuel == s) = ()

(* O2: interruption never loses the equation and always raises m_new_solution. *)
let o2_interrupt (s:st) (e:nat) (b:bool)
  : Lemma (let r = new_eq_eh s e b 0 in mem e r.eqs /\ r.flag /\ (forall x. mem x s.eqs ==> mem x r.eqs)) =
  FStar.Classical.forall_intro (FStar.List.Tot.Properties.append_mem s.eqs [e]);
  ()

(* O3: sat (FC_DONE needs m_eqs empty) is not reachable while a retained eq exists. *)
let fc_done_allowed (s:st) : bool = Nil? s.eqs
let o3_not_done (s:st) (e:nat) (fuel:nat) (b:bool)
  : Lemma (requires (fuel = 0 \/ not b))
          (ensures not (fc_done_allowed (new_eq_eh s e b fuel))) =
  FStar.List.Tot.Properties.append_length s.eqs [e]
