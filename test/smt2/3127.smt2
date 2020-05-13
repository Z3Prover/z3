(assert (not (forall ((a Real) (b Real)) (< b (/ 1.0 a) (/ 1.0 (- 2.0 a))))))
(check-sat)