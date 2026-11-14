module HornProofGuard
(* Model of horn_tactic::operator() (src/muz/fp/horn_tactic.cpp, head 534dea5, lines 403-411). *)
type outcome = | PassThrough | Throw | RunImp

let base_op (is_simplify proofs: bool) : outcome =
  if proofs then PassThrough else RunImp

let head_op (is_simplify proofs: bool) : outcome =
  if is_simplify && proofs then PassThrough
  else if proofs then Throw
  else RunImp

(* O1: full horn tactic with proofs never silently passes through nor runs imp *)
let o1 (proofs: bool) : Lemma (head_op false proofs == (if proofs then Throw else RunImp)) = ()

(* O2: horn-simplify behaviour is unchanged versus base for all inputs *)
let o2 (s p: bool) : Lemma (requires s) (ensures head_op s p == base_op s p) = ()

(* O3: without proofs, behaviour is unchanged for both variants *)
let o3 (s: bool) : Lemma (head_op s false == base_op s false) = ()

(* Witness: base horn with proofs returned goal unchanged (HORN -> unknown); head throws *)
let w : unit = assert (base_op false true == PassThrough /\ head_op false true == Throw)
