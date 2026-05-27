; Higher-order: apply combinator
(set-logic HO_ALL)
(define-fun apply ((f (-> Int Int)) (x Int)) Int (f x))
(assert (not (= (apply (lambda ((y Int)) (+ y 1)) 5) 6)))
(check-sat)
(exit)
