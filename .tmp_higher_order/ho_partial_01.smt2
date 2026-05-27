; Partial application: basic curried add
(set-logic HO_ALL)
(declare-fun add () (-> Int Int Int))
(assert (forall ((x Int) (y Int)) (= (add x y) (+ x y))))
(declare-fun add5 () (-> Int Int))
(assert (= add5 (add 5)))
(assert (not (= (add5 3) 8)))
(check-sat)
(exit)
