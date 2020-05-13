
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun X () (_ BitVec 8))
(declare-fun Y () (_ FloatingPoint 5 11))

(assert (= X ((_ fp.to_sbv 8) RTZ ((_ to_fp 5 11) RTZ -1.0 4)))) ; -16.0
(assert (not (= X #xf0)))

(check-sat)
(check-sat-using smt)
(exit)
