; Partial application: section
(set-logic HO_ALL)
(declare-fun mul () (-> Int Int Int))
(assert (forall ((x Int) (y Int)) (= (mul x y) (* x y))))
(declare-fun triple () (-> Int Int))
(assert (= triple (mul 3)))
(assert (not (= (triple 7) 21)))
(check-sat)
(exit)
