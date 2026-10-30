module Z3OptNlsatInline

(* Model of the a2952e5 delta in opt_nlsat.cpp. Old = removed public wrapper
   (outer guard: is_real obj && in_nra_fragment(hard,obj,reals_only), then
   preprocess, then private can_approach_from_below/check_limit with inner guard
   in_nra_fragment(purified goal,T,reals_only)). New = certify_result calling the
   private query directly (inner guard only; bounded_limit_query budget unchanged). *)
type lbool = | LTrue | LFalse | LUndef

let check_limit (inner:bool) (r:lbool) : lbool = if inner then r else LUndef
let old_q (is_real outer inner:bool) (r:lbool) : lbool =
  if not (is_real && outer) then LUndef else check_limit inner r
let new_q (inner:bool) (r:lbool) : lbool = check_limit inner r

(* O1: the new query only ever returns the nlsat answer r or l_undef. *)
let o1 (i:bool) (r:lbool) : Lemma (new_q i r == r \/ new_q i r == LUndef) = ()

(* O2: whenever the old wrapper's guards pass, old and new agree (no behavior change). *)
let o2 (a b c:bool) (r:lbool)
  : Lemma (requires a /\ b) (ensures new_q c r == old_q a b c r) = ()

(* O3: new and old differ only when the old wrapper's outer guard failed, and then
   old was l_undef; any definite new answer still requires the inner guard. *)
let o3 (a b c:bool) (r:lbool)
  : Lemma (ensures (new_q c r <> old_q a b c r ==> (not (a && b) /\ old_q a b c r == LUndef))
                /\ (new_q c r <> LUndef ==> c))
  = ()
