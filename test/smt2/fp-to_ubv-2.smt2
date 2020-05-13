
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ BitVec 8))
(assert (= X ((_ fp.to_ubv 8) RTZ (fp #b0 #b01111 #b0000000000)))) ; +1.0
(assert (not (= X #x01)))

(check-sat)
(check-sat-using smt)
(exit)
