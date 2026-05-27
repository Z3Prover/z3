; Partial application: uncurry
(set-logic HO_ALL)
(declare-fun f () (-> Int (-> Int Int)))
(assert (forall ((x Int) (y Int)) (= ((f x) y) (+ x y))))
(define-fun uncurry ((g (-> Int (-> Int Int))) (x Int) (y Int)) Int ((g x) y))
(assert (not (= (uncurry f 3 4) 7)))
(check-sat)
(exit)
