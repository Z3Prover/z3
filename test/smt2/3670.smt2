(set-option :proof true)
(declare-fun a (Int Int) Int)
(assert (forall ((b Int)) (= (a b 0) 0)))
(check-sat-using ufbv)