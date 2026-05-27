; MBQI-Enum: function satisfying polynomial relation
(set-logic HO_ALL)
(assert (exists ((f (-> Int Int)))
  (forall ((x Int)) (= (f (f x)) (+ x 2)))))
(check-sat)
(exit)
