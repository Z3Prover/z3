
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_BV)
(declare-fun v () (_ BitVec 3))
(declare-fun p () (_ BitVec 3))
(assert (= v (bvsmod  (_ bv3 3) v)))
(assert (not (= v (_ bv0 3))) )
(check-sat)
