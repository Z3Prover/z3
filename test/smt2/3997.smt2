(set-logic QF_NIA)
(set-option :smt.arith.solver 6)
(declare-const v3 Bool)
(declare-const i1 Int)
(declare-const v16 Bool)
(assert (>= (mod 531 i1) (* 81 i1 i1 i1 i1)))
(assert (or v3 (> 0 (- (- (* 81 i1 i1 i1 i1) 81)))))
(assert (or v16 (= false false false (xor true false false true (<= i1 659) false false true true))))
(check-sat)