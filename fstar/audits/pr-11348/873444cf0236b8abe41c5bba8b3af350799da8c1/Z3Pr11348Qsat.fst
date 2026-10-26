module Z3Pr11348Qsat
(* qsat_tactic::operator(): fail_if_proof_generation now runs first. *)
type res = | Throws | Proceeds
let guard (proofs:bool) : res = if proofs then Throws else Proceeds
let o1 (p:bool) : Lemma (p ==> guard p == Throws) = ()
let o2 (p:bool) : Lemma (not p ==> guard p == Proceeds) = ()
(* base reached the body with proofs enabled; head cannot *)
let o3 (p:bool) : Lemma (guard p == Proceeds ==> not p) = ()
