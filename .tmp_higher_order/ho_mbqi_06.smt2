; MBQI-Enum: periodic function
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(assert (forall ((x Int)) (= (f (+ x 3)) (f x))))
(assert (= (f 0) 10))
(assert (not (= (f 9) 10)))
(check-sat)
(exit)
