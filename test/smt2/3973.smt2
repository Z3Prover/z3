(assert (forall ((a Int)) (exists ((b Int)) (= (* 2 b) a))))
(check-sat)