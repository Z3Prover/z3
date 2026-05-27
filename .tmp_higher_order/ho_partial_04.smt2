; Partial application: curried comparison
(set-logic HO_ALL)
(declare-fun geq () (-> Int Int Bool))
(assert (forall ((x Int) (y Int)) (= (geq x y) (>= x y))))
(declare-fun geq5 () (-> Int Bool))
(assert (= geq5 (geq 5)))
(assert (not (and (geq5 3) (not (geq5 6)))))
(check-sat)
(exit)
