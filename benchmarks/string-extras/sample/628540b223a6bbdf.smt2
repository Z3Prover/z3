; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/seq_foldl_nth_model_validation.smt2
; Regression: seq.foldl with seq.nth under model_validate must produce a valid
; model (sat).
; Transferred from src/test/seq_rewriter.cpp (test_seq_foldl_nth_model_validation).
(set-option :model_validate true)
(declare-const initial Int)
(declare-const all (Seq Int))
(declare-const final Int)
(declare-const elements (Seq Int))
(define-fun all_sums ((prev_sums (Seq Int)) (elem Int)) (Seq Int)
  (seq.++ (seq.unit (+ (seq.nth prev_sums 0) elem)) prev_sums))
(assert (= all (seq.foldl all_sums (seq.unit initial) elements)))
(assert (= final (seq.nth all 0)))
(assert (= initial 0))
(assert (= final 6))
(check-sat)
(get-model)
