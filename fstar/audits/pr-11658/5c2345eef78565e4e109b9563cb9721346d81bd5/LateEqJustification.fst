module LateEqJustification
(* Abstract model of Z3 smt::context::mk_enode, is_true_eq branch.
   v: literal(v) of the equality atom is true; h: reason the arguments are equal.
   The edge e ~ true is explained by an explanation; a derived clause is sound
   iff (explanation holds) ==> (e = true). edge_true is modeled as v (assumption A1). *)
type st = { v : bool; h : bool }

let reachable (s:st) = s.v ==> s.h

type expl = | NoAnte | LitV

let holds (x:expl) (s:st) : bool = match x with | NoAnte -> true | LitV -> s.v
let edge_true (s:st) : bool = s.v

let sound (x:expl) = forall (s:st). reachable s /\ holds x s ==> edge_true s

let witness : st = { v = false; h = false }
let base_counterexample () : Lemma (reachable witness /\ holds NoAnte witness /\ ~(edge_true witness)) = ()
let base_unsound () : Lemma (~(sound NoAnte)) = base_counterexample ()

let pr_sound () : Lemma (sound LitV) = ()

let pr_complete () : Lemma (forall (s:st). reachable s /\ edge_true s ==> holds LitV s) = ()
