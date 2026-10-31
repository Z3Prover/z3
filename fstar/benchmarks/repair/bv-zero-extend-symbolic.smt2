(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (not (= ((_ zero_extend 24) x) (concat (_ bv0 24) x))))
(check-sat)
