; HO quantification: no bijection between Int and Bool
(set-logic HO_ALL)
(assert (exists ((f (-> Int Bool)))
  (and (forall ((x Int) (y Int)) (=> (= (f x) (f y)) (= x y)))
       (forall ((b Bool)) (exists ((x Int)) (= (f x) b))))))
(check-sat)
(exit)
