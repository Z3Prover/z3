module Z3Pr11348Head
(* Model of set_option_cmd global-decls guard (basic_cmds.cpp) and the
   proofs_enabled branch in theory_lra/theory_arith (power0/idiv/div axioms). *)
type st = { init: bool; gd: bool }
type res = | Ok of st | Err

let set_new (s:st) (v:bool) : res =
  if v <> s.gd then (if s.init then Err else Ok ({ s with gd = v })) else Ok s

(* O1: success implies requested value is in force *)
let o1 (s:st) (v:bool) : Lemma (match set_new s v with Ok s' -> s'.gd = v | Err -> True) = ()
(* O2: error only if initialized and the value would change *)
let o2 (s:st) (v:bool) : Lemma (Err? (set_new s v) ==> (s.init /\ v <> s.gd)) = ()
(* O3: before initialization behaves exactly as unconditional set *)
let o3 (s:st) (v:bool) : Lemma (requires not s.init) (ensures set_new s v == Ok ({ s with gd = v })) = ()

type just = | NoJust | ThAxiom
let assert_lit (proofs:bool) : just = if proofs then ThAxiom else NoJust
(* O4: with proofs enabled the literal always carries a theory-axiom justification *)
let o4 (p:bool) : Lemma (p ==> assert_lit p == ThAxiom) = ()
(* O5: without proofs, behavior is unchanged (assign with null justification) *)
let o5 (p:bool) : Lemma (not p ==> assert_lit p == NoJust) = ()
