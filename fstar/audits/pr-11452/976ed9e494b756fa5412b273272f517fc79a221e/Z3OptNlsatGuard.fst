module Z3OptNlsatGuard

(* Model of opt_nlsat.cpp at 976ed9e: can_approach_from_below / check_limit.
   lbool results; guard = in_nra_fragment(..., reals_only=true). *)
type lbool = | LTrue | LFalse | LUndef

(* check_limit: early guard on purified goal + T, else the original nlsat query r *)
let check_limit (guard:bool) (r:lbool) : lbool = if guard then r else LUndef

(* can_approach_from_below: outer guard (obj real && fragment) then inner check_limit *)
let can_approach (is_real outer inner:bool) (r:lbool) : lbool =
  if not (is_real && outer) then LUndef else check_limit inner r

(* O1: the new early exit only ever replaces a result by l_undef (never flips true/false). *)
let o1 (g:bool) (r:lbool) : Lemma (check_limit g r == r \/ check_limit g r == LUndef) = ()

(* O2: a definite answer from the new code is a definite answer of the pre-PR query. *)
let o2 (a b c:bool) (r:lbool)
  : Lemma (requires can_approach a b c r <> LUndef)
          (ensures can_approach a b c r == r /\ a /\ b /\ c) = ()

(* O3: when all guards hold (no integer terms), behavior is unchanged. *)
let o3 (r:lbool) : Lemma (can_approach true true true r == r) = ()
