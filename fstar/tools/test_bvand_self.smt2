(declare-const y (_ BitVec 32))
(assert (not (= (bvand y y) y)))
(check-sat)
