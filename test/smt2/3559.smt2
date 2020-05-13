(set-logic QF_BV)
(set-option :trace true)
(assert (distinct true true true true true true true true (distinct (bvsub (_ bv480 9) (_ bv480 9)) (_ bv0 9) (_ bv480 9) (_ bv480 9))))
(check-sat)