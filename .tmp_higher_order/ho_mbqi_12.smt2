; MBQI-Enum: function interpolation
(set-logic HO_ALL)
(assert (exists ((f (-> Int Int)))
  (and (= (f 0) 0) (= (f 10) 100)
       (forall ((x Int)) (=> (and (>= x 0) (<= x 10))
                             (and (>= (f x) 0) (<= (f x) 100)))))))
(check-sat)
(exit)
