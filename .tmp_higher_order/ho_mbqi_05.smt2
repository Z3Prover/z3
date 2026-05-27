; MBQI-Enum: homomorphism discovery
(set-logic HO_ALL)
(assert (exists ((h (-> Int Int)))
  (forall ((x Int) (y Int))
    (= (h (+ x y)) (+ (h x) (h y))))))
(check-sat)
(exit)
