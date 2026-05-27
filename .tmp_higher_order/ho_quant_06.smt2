; HO quantification: monotone function exists
(set-logic HO_ALL)
(assert (exists ((f (-> Int Int)))
  (and (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y))))
       (= (f 0) 0)
       (= (f 10) 100))))
(check-sat)
(exit)
