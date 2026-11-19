module Pr11620Clamp
(* Model of the br_status clamp added at model_evaluator.cpp (head 8cdb74c), ITE branch.
   Enum order from rewriter_types.h: REWRITE1(REWRITE2<REWRITE3<REWRITE_FULL<DONE<FAILED. *)
type br = | R1 | R2 | R3 | RFULL | DONE | FAILED

let rank (s:br) : nat = match s with
  | R1 -) 0 | R2 -> 1 | R3 -> 2 | RFULL -> 3 | DONE -> 4 | FAILED -> 5

let lt_done (s:br) : bool = rank s < rank DONE

(* patched code: st = m_b_rw.mk_app_core(...); if (k==OP_ITE && st<BR_DONE) return BR_REWRITE1; return st *)
let clamp (is_ite:bool) (s:br) : br = if is_ite && lt_done s then R1 else s

(* Obligation 1: ITE rewrite statuses are changed; DONE/FAILED and non-ITE are preserved. *)
let ob1 (is_ite:bool) (s:br) : Lemma
  (ensures (not is_ite ==> clamp is_ite s == s) /\ (s == DONE ==> clamp is_ite s == DONE)
           /\ (s == FAILED ==> clamp is_ite s == FAILED)) = ()

(* Obligation 2: clamp never raises the rewrite depth, and any ITE rewrite request becomes depth 1. *)
let ob2 (is_ite:bool) (s:br) : Lemma
  (ensures rank (clamp is_ite s) <= rank s /\ (is_ite /\ lt_done s ==> clamp is_ite s == R1)) = ()

(* Obligation 3: the result term is untouched by the status rewrite. Model the builtin as
   (status, result); the patched wrapper returns the same result component. *)
type res = { st: br; term: int }
let wrap (is_ite:bool) (p:res) : res = { st = clamp is_ite p.st; term = p.term }
let ob3 (is_ite:bool) (p:res) : Lemma (ensures (wrap is_ite p).term == p.term) = ()

(* Obligation 4 (limit, not refutation): clamped status can differ from the original,
   so a deeper pending rewrite is skipped: concrete witness of reduced depth. *)
let witness_reduced () : Lemma (clamp true RFULL == R1 /\ clamp true RFULL <> RFULL) = ()
