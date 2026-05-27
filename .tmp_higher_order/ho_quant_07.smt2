; HO quantification: fixed point existence
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(assert (forall ((x Int)) (and (>= (f x) 0) (<= (f x) 10))))
(assert (not (exists ((x Int)) (= (f x) x))))
(check-sat)
(exit)
