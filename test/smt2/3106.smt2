(declare-const a Real)
(declare-const b Real)
(assert (not (<= (* (- a b) (- a b) (* a a b b)) 0)))
(check-sat-using nlsat)