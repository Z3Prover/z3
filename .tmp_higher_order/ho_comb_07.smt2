; Higher-order: twice combinator
(set-logic HO_ALL)
(define-fun twice ((f (-> Int Int)) (x Int)) Int (f (f x)))
(assert (not (= (twice (lambda ((x Int)) (+ x 3)) 0) 6)))
(check-sat)
(exit)
