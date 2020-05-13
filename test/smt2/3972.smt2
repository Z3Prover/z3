(set-option :smt.arith.solver 2)
(declare-const s String)
(assert (and (> (str.len s) 34) (= (str.at s 0) "a")))
(check-sat)
