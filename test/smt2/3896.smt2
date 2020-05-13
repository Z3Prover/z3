(declare-fun a () Int)
(assert (distinct 0 (div 0 a)))
(assert (= 0 (div (- (* a a) a) a)))
(check-sat)