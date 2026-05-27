; MBQI-Enum: order-preserving bijection
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(assert (forall ((x Int) (y Int)) (= (< x y) (< (f x) (f y)))))
(assert (= (f 0) 5))
(assert (not (> (f 1) 5)))
(check-sat)
(exit)
