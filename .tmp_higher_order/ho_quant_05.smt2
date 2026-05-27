; HO quantification: surjectivity
; Every element in range has a preimage
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(assert (forall ((y Int)) (exists ((x Int)) (= (f x) y))))
(assert (forall ((x Int)) (>= (f x) 0)))
(check-sat)
(exit)
