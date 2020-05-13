(declare-fun a () Int)
(assert (forall ((b Int)) (or (= (* b b) a) (> b 0))))
(check-sat-using (then qe_rec smt))