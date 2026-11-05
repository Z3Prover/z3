(set-logic QF_BV)
(assert (not (= ((_ zero_extend 24) #xff) #x000000ff)))
(check-sat)
