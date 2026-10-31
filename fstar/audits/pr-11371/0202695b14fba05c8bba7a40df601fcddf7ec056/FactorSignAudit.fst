module FactorSignAudit
#set-options "--z3rlimit 10 --fuel 1 --ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr native"
open FStar.Real

(* Models arith_rewriter::factor_le_ge_eq (arith_rewriter.cpp:729-762) at the
   semantic level, assuming p = f*g (checked separately by ring normalization
   in the PR's Z3ArithmeticFactor.fst, not re-proved here). *)
let zero_case (f g:real)
  : Lemma ((f *. g == 0.0R) <==> (f == 0.0R \/ g == 0.0R)) = ()

let ge_case (f g:real)
  : Lemma ((f *. g >=. 0.0R) <==> (((f >=. 0.0R) <==> (g >=. 0.0R)) \/ (f == 0.0R \/ g == 0.0R)))
  = ()

let le_case (f g:real)
  : Lemma ((f *. g <=. 0.0R) <==> ((~((f >=. 0.0R) <==> (g >=. 0.0R))) \/ (f == 0.0R \/ g == 0.0R)))
  = ()

let ge_case_int (f g:int)
  : Lemma ((f * g >= 0) <==> (((f >= 0) <==> (g >= 0)) \/ (f = 0 \/ g = 0))) = ()
let le_case_int (f g:int)
  : Lemma ((f * g <= 0) <==> ((~((f >= 0) <==> (g >= 0))) \/ (f = 0 \/ g = 0))) = ()
