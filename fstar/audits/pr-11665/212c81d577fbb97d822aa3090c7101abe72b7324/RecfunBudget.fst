module RecfunBudget
(* Model of recfun_rewriter::inc_unfold (PR 11665 ``@212c81d``). Applications are
   abstracted to nat ids (hash-consed exprs => pointer equality = id equality). *)
open FStar.List.Tot

type st = { num: nat; mx: nat; blocked: list nat }

let reset_unfolds (s:st) : st = { s with num = 0 }

(* returns (result, new state); mirrors the C++ control flow *)
let inc_unfold (s:st) (a:nat) : bool & st =
  if Nil? s.blocked && s.num < s.mx then (true, { s with num = s.num + 1 })
  else if mem a s.blocked then (false, s)
  else if s.num < s.mx then (true, { s with num = s.num + 1 })
  else (false, { s with blocked = a :: s.blocked })

let inv (s:st) = s.num <= s.mx

(* O1: budget invariant preserved; a true answer charges exactly one unit *)
let o1 (s:st) (a:nat)
  : Lemma (requires inv s)
          (ensures (let (r,s') = inc_unfold s a in
                    inv s' /\ s'.mx == s.mx /\
                    (r ==> s'.num == s.num + 1 /\ s.num < s.mx) /\
                    (not r ==> s'.num == s.num)))
  = ()

(* O2: a blocked application is never unfolded, until the blocked set is reset *)
let o2 (s:st) (a:nat)
  : Lemma (requires mem a s.blocked)
          (ensures fst (inc_unfold s a) == false)
  = ()

(* O3: refusing at the limit blocks the application, and a refused app is
   then recorded, so repeated attempts cost nothing and never unfold *)
let o3 (s:st) (a:nat)
  : Lemma (requires inv s /\ s.num == s.mx)
          (ensures (let (r,s1) = inc_unfold s a in
                    r == false /\ mem a s1.blocked /\
                    fst (inc_unfold s1 a) == false /\ s1.num == s.num))
  = ()

(* O4: after reset_unfolds the budget is replenished; with nothing blocked
   the first unfolding is allowed iff max > 0 *)
let o4 (s:st) (a:nat)
  : Lemma (requires Nil? s.blocked)
          (ensures fst (inc_unfold (reset_unfolds s) a) == (s.mx > 0))
  = ()
