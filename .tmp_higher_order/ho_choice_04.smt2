; Choice term: minimum via choice
(set-logic HO_ALL)
(declare-fun S () (-> Int Bool))
(assert (exists ((x Int)) (S x)))
(define-fun min_S () Int
  (choice ((x Int)) (and (S x) (forall ((y Int)) (=> (S y) (<= x y))))))
(assert (S 5))
(assert (S 3))
(assert (forall ((x Int)) (=> (S x) (>= x 3))))
(assert (not (= min_S 3)))
(check-sat)
(exit)
