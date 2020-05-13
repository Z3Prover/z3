(assert (forall ((a Real)) (exists ((b Real)) (and (>= (+ a b) 0.0) (<= b 0.0)))))
(check-sat-using bv)
(check-sat-using smt)
(check-sat)