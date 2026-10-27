module Z3SeqEagerBudgetPR11356
(* Model of theory_seq::can_reduce_eqs / solve_eqs / simplify_and_solve_eqs
   at head 7dac245e when m.limit().suspended() = true (m.inc() is then always true).
   Each loop test in solve_eqs calls can_reduce_eqs; each admitted iteration
   solves one pending equation (equations of the form x = unit(i) ++ y are
   solved by simplify_eq). ctx.inconsistent() is assumed false. *)

let budget : nat = 1024

type st = { counter: nat; new_sol: bool; pending: nat }

(* can_reduce_eqs, suspended branch *)
let can_reduce (s:st) : (st & bool) =
  if s.counter >= budget then ({ s with new_sol = true }, false)
  else ({ s with counter = s.counter + 1 }, true)

(* for (; i < m_eqs.size() && can_reduce_eqs(); ++i) solve_eq(i) removes solved eq *)
let rec loop (s:st) : Tot st (decreases (budget + 1 - s.counter + s.pending)) =
  if s.pending = 0 then s
  else
    let (s', ok) = can_reduce s in
    if ok then loop { s' with pending = s'.pending - 1 } else s'

(* if (i < m_eqs.size()) m_new_solution = true *)
let solve_eqs (s:st) : st =
  let r = loop s in
  if r.pending > 0 then { r with new_sol = true } else r

(* one iteration of: while (m_new_solution && m.inc()) { m_new_solution=false; solve_eqs(0); } *)
let round (s:st) : st = solve_eqs { s with new_sol = false }

let rec iter (n:nat) (s:st) : Tot st (decreases n) =
  if n = 0 then s else iter (n-1) (round s)

(* O1: once the budget is exhausted with pending equations, a round is the identity
   on a state with new_sol = true, so the suspended while-loop cannot make progress. *)
let round_fixpoint (s:st)
  : Lemma (requires s.counter = budget /\ s.pending > 0 /\ s.new_sol = true)
          (ensures round s == s)
  = ()

let rec iter_fixpoint (n:nat) (s:st)
  : Lemma (requires s.counter = budget /\ s.pending > 0 /\ s.new_sol = true)
          (ensures iter n s == s) (decreases n)
  = if n = 0 then () else (round_fixpoint s; iter_fixpoint (n-1) s)

(* O2: from the reset state (propagate() sets counter = 0) with >= 1024 pending
   equations, the first round exhausts the budget leaving pending equations. *)
let rec loop_exhausts (s:st)
  : Lemma (requires s.counter <= budget /\ s.pending >= budget - s.counter + 1)
          (ensures (let r = loop s in r.counter = budget /\ r.pending > 0))
          (decreases (budget - s.counter))
  = if s.counter = budget then ()
    else loop_exhausts { s with counter = s.counter + 1; pending = s.pending - 1 }

let witness : st = { counter = 0; new_sol = true; pending = 2048 }

(* Reachable witness (2048 pending equations, as in the PR's own regression):
   after round 1 the state is a fixpoint with new_sol = true, for every number of rounds. *)
let witness_diverges (n:nat)
  : Lemma (ensures (let r1 = round witness in
                    r1.counter = budget /\ r1.pending > 0 /\ r1.new_sol = true /\
                    iter n r1 == r1))
  = loop_exhausts { witness with new_sol = false };
    let r1 = round witness in
    iter_fixpoint n r1
