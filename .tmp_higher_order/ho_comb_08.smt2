; Higher-order: iterate combinator
(set-logic HO_ALL)
(declare-fun iterate () (-> Int (-> Int Int) Int Int))
(assert (forall ((f (-> Int Int)) (x Int)) (= (iterate 0 f x) x)))
(assert (forall ((n Int) (f (-> Int Int)) (x Int))
  (=> (> n 0) (= (iterate n f x) (f (iterate (- n 1) f x))))))
(assert (not (= (iterate 3 (lambda ((x Int)) (+ x 1)) 0) 3)))
(check-sat)
(exit)
