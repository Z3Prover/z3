module Z3Pr11348Head7fbf

(* Model of set_option_cmd global_decls branch (basic_cmds.cpp ~526) and
   the proof-mode branch for theory_arith/theory_lra axiom assertion. *)

type st = { has_manager: bool; global_decls: bool }

(* set_global_decls precondition: SASSERT(!has_manager()) *)
let set_pre (s:st) = not s.has_manager

(* Some r = accepted new state; None = cmd_exception *)
let new_set (s:st) (v:bool) : option st =
  if v <> s.global_decls then
    (if s.has_manager then None else Some { s with global_decls = v })
  else Some s

let old_set (s:st) (v:bool) : option st =
  if s.has_manager then None else Some { s with global_decls = v }

(* O1: every call to set_global_decls in the new code satisfies its precondition *)
let o1 (s:st) (v:bool)
  : Lemma (match new_set s v with
           | Some s' -> (s'.global_decls <> s.global_decls ==> set_pre s)
           | None -> True) = ()

(* O2: the new code only differs from the old by accepting no-op same-value
   sets after initialization; otherwise results are identical *)
let o2 (s:st) (v:bool)
  : Lemma (if v <> s.global_decls || not s.has_manager
           then new_set s v == old_set s v
           else new_set s v == Some s) = ()

(* O3: accepted outcome always has global_decls = v *)
let o3 (s:st) (v:bool)
  : Lemma (match new_set s v with Some s' -> s'.global_decls = v | None -> True) = ()

(* Proof branch: assertion is recorded as th-axiom iff proofs enabled *)
type act = | Assign | ThAxiom
let act_new (proofs:bool) : act = if proofs then ThAxiom else Assign
let o4 (p:bool) : Lemma ((p ==> act_new p == ThAxiom) /\ (not p ==> act_new p == Assign)) = ()
