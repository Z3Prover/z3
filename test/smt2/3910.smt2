(set-logic QF_AUFLIA)
(set-option :model_validate true)
(set-option :rewriter.push_ite_arith true)
(set-option :rewriter.flat false)
(set-option :smt.arith.solver 2)
(declare-const i4 Int)
;(push)
;(assert (>= (* 495 17 i4 (ite (>= i4 0) 1 (- 1))) 287))
(assert (>= (* 495 17 (abs i4)) 287))
;(assert (or (> i4 0) (<= (* 495 17 i4) -287)))
;(assert (or (< i4 0) (>= (* 495 17 i4) 287)))
(check-sat)