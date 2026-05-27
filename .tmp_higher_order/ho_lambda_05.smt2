; Higher-order: beta reduction challenge
(set-logic HO_ALL)
(declare-fun a () Int)
(assert (= ((lambda ((x Int)) (+ x x)) a) (* 2 a)))
(assert (> a 0))
(check-sat)
(get-model)
(exit)
