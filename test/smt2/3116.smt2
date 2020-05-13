(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or (not (and a b)) (not a)))
(check-sat-using qfufbv_ackr)
