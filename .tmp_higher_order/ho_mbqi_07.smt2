; MBQI-Enum: function with given image
(set-logic HO_ALL)
(assert (exists ((f (-> Int Int)))
  (and (forall ((x Int)) (or (= (f x) 0) (= (f x) 1)))
       (= (f 5) 1)
       (= (f 6) 0))))
(check-sat)
(exit)
