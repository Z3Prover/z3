module ArithLhsGuard
type op_kind = | LE | GE | EQ
let old_guard (lhs ineq:bool) : bool = ineq || lhs
let new_guard (k:op_kind) (lhs ineq:bool) : bool = lhs || (k <> EQ && ineq)

(* O1: equalities depend only on arith_lhs *)
let o1 (lhs ineq:bool) : Lemma (new_guard EQ lhs ineq == lhs) = ()
(* O2: inequalities keep old behaviour *)
let o2 (k:op_kind{k <> EQ}) (lhs ineq:bool) : Lemma (new_guard k lhs ineq == old_guard lhs ineq) = ()
(* O3: only change vs. old is EQ with ineq && not lhs, which becomes false *)
let o3 (k:op_kind) (lhs ineq:bool)
  : Lemma (new_guard k lhs ineq <> old_guard lhs ineq ==> (k = EQ /\ ineq /\ not lhs /\ not (new_guard k lhs ineq))) = ()
