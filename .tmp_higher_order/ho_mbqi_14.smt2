; MBQI-Enum: binary operation synthesis
(set-logic HO_ALL)
(assert (exists ((op (-> Int Int Int)))
  (and (forall ((x Int)) (= (op x 0) x))
       (forall ((x Int) (y Int)) (= (op x (+ y 1)) (+ (op x y) 1))))))
(check-sat)
(exit)
