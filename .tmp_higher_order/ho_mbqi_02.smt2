; MBQI-Enum: idempotent function
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(assert (forall ((x Int)) (= (f (f x)) (f x))))
(assert (distinct (f 0) 0))
(check-sat)
(get-model)
(exit)
