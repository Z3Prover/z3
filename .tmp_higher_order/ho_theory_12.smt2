; HO + Arithmetic: summation via function
(set-logic HO_ALL)
(declare-fun sum_to () (-> Int (-> Int Int) Int))
(assert (forall ((f (-> Int Int))) (= (sum_to 0 f) (f 0))))
(assert (forall ((n Int) (f (-> Int Int)))
  (=> (> n 0) (= (sum_to n f) (+ (f n) (sum_to (- n 1) f))))))
(assert (not (= (sum_to 3 (lambda ((x Int)) x)) 6)))
(check-sat)
(exit)
