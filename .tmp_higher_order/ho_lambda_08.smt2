; Higher-order: lambda equality
; Two extensionally equal lambdas
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(declare-fun g () (-> Int Int))
(assert (= f (lambda ((x Int)) (+ x 1))))
(assert (= g (lambda ((x Int)) (+ 1 x))))
(assert (not (= f g)))
(check-sat)
(exit)
