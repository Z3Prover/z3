; Fixed-point combinator pattern
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
; f has a fixed point
(assert (exists ((x Int)) (= (f x) x)))
; f is strictly increasing - contradiction
(assert (forall ((x Int)) (> (f x) x)))
(check-sat)
(exit)
