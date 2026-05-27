; Partial application: on combinator
; (on f g) x y = f (g x) (g y)
(set-logic HO_ALL)
(define-fun on ((f (-> Int Int Int)) (g (-> Int Int)) (x Int) (y Int)) Int
  (f (g x) (g y)))
(assert (not (= (on (lambda ((a Int) (b Int)) (+ a b))
                    (lambda ((x Int)) (* x x))
                    2 3) 13)))
(check-sat)
(exit)
