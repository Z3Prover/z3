; Higher-order: nested lambda
(set-logic HO_ALL)
(declare-fun result () Int)
(assert (= result ((lambda ((x Int)) ((lambda ((y Int)) (+ x y)) 3)) 4)))
(assert (not (= result 7)))
(check-sat)
(exit)
