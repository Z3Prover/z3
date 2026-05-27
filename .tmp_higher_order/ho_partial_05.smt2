; Partial application: curried ternary
(set-logic HO_ALL)
(declare-fun f () (-> Int Int Int Int))
(assert (forall ((x Int) (y Int) (z Int)) (= (f x y z) (+ x (* y z)))))
(declare-fun f2 () (-> Int Int))
(assert (= f2 (f 1 2)))
(assert (not (= (f2 3) 7)))
(check-sat)
(exit)
