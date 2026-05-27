; Choice term: nested choice
(set-logic HO_ALL)
(declare-fun R () (-> Int Int Bool))
(assert (forall ((x Int)) (exists ((y Int)) (R x y))))
(define-fun f ((x Int)) Int (choice ((y Int)) (R x y)))
(declare-fun a () Int)
(assert (not (R a (f a))))
(check-sat)
(exit)
