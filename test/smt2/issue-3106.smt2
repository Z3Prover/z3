(declare-fun a () Real)
(declare-fun b () Real)
(assert (not (<= (* (- a b) (- a b) (* a a b b)) 0)))
(check-sat-using nlsat)