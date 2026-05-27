; MBQI-Enum: comparison with uninterpreted function
(set-logic HO_ALL)
(declare-fun g () (-> Int Int))
(assert (exists ((f (-> Int Int)))
  (forall ((x Int)) (>= (f x) (g x)))))
(check-sat)
(exit)
