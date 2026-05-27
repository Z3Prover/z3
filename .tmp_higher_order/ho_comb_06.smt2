; Higher-order: flip combinator
(set-logic HO_ALL)
(define-fun flip ((f (-> Int Int Int)) (x Int) (y Int)) Int (f y x))
(declare-fun sub () (-> Int Int Int))
(assert (= sub (lambda ((a Int) (b Int)) (- a b))))
(assert (not (= (flip sub 3 10) 7)))
(check-sat)
(exit)
