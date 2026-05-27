; Higher-order: lambda capturing free variable
(set-logic HO_ALL)
(declare-fun c () Int)
(declare-fun f () (-> Int Int))
(assert (= f (lambda ((x Int)) (+ x c))))
(assert (= (f 0) 42))
(assert (not (= c 42)))
(check-sat)
(exit)
