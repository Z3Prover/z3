; Choice term: well-ordering principle fragment
(set-logic HO_ALL)
(declare-fun S () (-> Int Bool))
(assert (S 10))
(assert (S 5))
(assert (S 20))
(define-fun least () Int
  (choice ((x Int)) (and (S x) (forall ((y Int)) (=> (and (S y) (< y x)) false)))))
(assert (not (and (S least) (<= least 5))))
(check-sat)
(exit)
