; MBQI-Enum: involution
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(assert (forall ((x Int)) (= (f (f x)) x)))
(assert (distinct (f 0) 0))
(check-sat)
(get-model)
(exit)
