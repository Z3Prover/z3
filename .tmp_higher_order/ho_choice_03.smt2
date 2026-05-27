; Choice term: inverse function via choice
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(assert (forall ((x Int) (y Int)) (=> (= (f x) (f y)) (= x y))))
(define-fun f_inv ((y Int)) Int (choice ((x Int)) (= (f x) y)))
(declare-fun a () Int)
(assert (not (= (f (f_inv (f a))) (f a))))
(check-sat)
(exit)
