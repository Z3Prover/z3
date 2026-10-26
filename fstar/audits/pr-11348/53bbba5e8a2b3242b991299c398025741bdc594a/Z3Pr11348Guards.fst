module Z3Pr11348Guards
(* Abstract models of three changed C++ guards in PR 11348. *)

(* 1. basic_cmds.cpp set_option :global-decls *)
type st = { init: bool; gd: bool }
type res = | Throw | Ok of st

let old_set (s:st) (v:bool) : res = if s.init then Throw else Ok ({ s with gd = v })
let new_set (s:st) (v:bool) : res =
  if v <> s.gd then (if s.init then Throw else Ok ({ s with gd = v })) else Ok s

(* O1: re-setting the current value never throws and never changes state *)
let o1 (s:st) : Lemma (new_set s s.gd == Ok s) = ()
(* O2: a differing value behaves exactly as before *)
let o2 (s:st) (v:bool) : Lemma (requires v <> s.gd) (ensures new_set s v == old_set s v) = ()
(* O3: initialized context's global_decls can never be altered *)
let o3 (s:st) (v:bool) : Lemma (requires s.init)
  (ensures (match new_set s v with Throw -> True | Ok s' -> s'.gd == s.gd)) = ()

(* 2. qsat.cpp: fail_if_proof_generation precedes any work *)
type qres = | QFail | QRun
let qsat_old (_proofs:bool) : qres = QRun
let qsat_new (proofs:bool) : qres = if proofs then QFail else QRun
let q1 (p:bool) : Lemma (p ==> qsat_new p == QFail) = ()
let q2 (p:bool) : Lemma (~p ==> qsat_new p == qsat_old p) = ()

(* 3. theory_lra / theory_arith: assign vs mk_th_axiom *)
type act = | Assign | ThAxiom
let act_old (_p:bool) : act = Assign
let act_new (p:bool) : act = if p then ThAxiom else Assign
let a1 (p:bool) : Lemma (~p ==> act_new p == act_old p) = ()
let a2 (p:bool) : Lemma (p ==> act_new p == ThAxiom /\ act_new p <> Assign) = ()
