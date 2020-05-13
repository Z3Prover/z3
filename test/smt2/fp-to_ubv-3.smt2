
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ BitVec 8))
(assert (= X ((_ fp.to_ubv 8) RTZ (fp #b0 #b10000 #b0000000000)))) ; +2.0
(assert (not (= X #x02)))

(check-sat)
(check-sat-using smt)
(exit)
