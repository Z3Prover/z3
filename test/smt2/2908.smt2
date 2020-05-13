(declare-fun a (Int) Int)
(declare-fun b () Int)
(assert (= (ite (= b (a 0)) b (+ 2 b)) (ite (= b (a 0)) b (- 1 b))))
(check-sat)