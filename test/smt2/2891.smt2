(declare-fun x () Real)
(assert (= (^ (- 1.0 x) (- 1.0)) (* 2.0 (^ x (- 1.0)))))
(check-sat)
