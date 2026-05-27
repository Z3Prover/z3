; HO quantification: function injectivity
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(assert (forall ((x Int) (y Int)) (=> (= (f x) (f y)) (= x y))))
(assert (= (f 1) (f 2)))
(check-sat)
(exit)
