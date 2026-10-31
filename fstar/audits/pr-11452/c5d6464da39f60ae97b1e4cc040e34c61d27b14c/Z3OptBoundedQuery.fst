module Z3OptBoundedQuery

(* Model of opt_nlsat.cpp::bounded_limit_query at head c5d6464. *)
type lbool = | LTrue | LFalse | LUndef
type outcome = | Ret : lbool -> outcome | TacEx | ZEx
(* env: canceled at entry; what the query did: outcome, cancel flag at its end
   (the flag is visible after the exception/return, before the pop), and whether the
   cancel message equals Z3_CANCELED_MSG (external). *)
type env = { canceled_in: bool; out: outcome; canceled_after: bool; ext_msg: bool }
type res = { r: lbool; recancel: bool; called: bool; rethrow: bool }

let run (ticks:nat) (e:env) : res =
  if ticks = 0 then { r = LUndef; recancel = false; called = false; rethrow = false }
  else if e.canceled_in then { r = LUndef; recancel = false; called = false; rethrow = false }
  else
    match e.out with
    | Ret v -> { r = v; recancel = e.canceled_after && e.ext_msg; called = true; rethrow = false }
    | TacEx -> { r = LUndef; recancel = e.canceled_after && e.ext_msg; called = true; rethrow = false }
    | ZEx ->
      if not e.canceled_after then { r = LUndef; recancel = false; called = true; rethrow = true }
      else { r = LUndef; recancel = e.ext_msg; called = true; rethrow = false }

(* O1: disabled budget or pre-canceled operation: query not started, l_undef,
   flag not cleared by an entered scope. *)
let o1 (ticks:nat) (e:env)
  : Lemma (requires ticks = 0 \/ e.canceled_in)
          (ensures (run ticks e).r == LUndef /\ not (run ticks e).called /\ not (run ticks e).rethrow) = ()

(* O2: a definite answer implies the query ran and returned that answer normally. *)
let o2 (ticks:nat) (e:env)
  : Lemma (requires (run ticks e).r <> LUndef)
          (ensures ticks > 0 /\ not e.canceled_in /\ e.out == Ret (run ticks e).r) = ()

(* O3: an external cancellation seen at the end of the query is re-raised after the pop,
   in every non-rethrow path; only an exception with no cancellation propagates. *)
let o3 (ticks:nat) (e:env)
  : Lemma (requires ticks > 0 /\ not e.canceled_in /\ e.canceled_after /\ e.ext_msg)
          (ensures (run ticks e).recancel /\ not (run ticks e).rethrow) = ()
let o3b (ticks:nat) (e:env)
  : Lemma (ensures (run ticks e).rethrow ==> (ticks > 0 /\ not e.canceled_in /\ e.out == ZEx /\ not e.canceled_after)) = ()
