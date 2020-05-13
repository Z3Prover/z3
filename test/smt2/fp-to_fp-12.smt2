
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status sat)

(declare-fun x_64 () (_ FloatingPoint 11 53))
(declare-fun x_32 () (_ FloatingPoint 8 24))
(assert (fp.eq ((_ to_fp 11 53) roundNearestTiesToEven x_32) x_64))
(assert (fp.eq ((_ to_fp 8 24) roundNearestTiesToEven x_64) x_32))

(check-sat)
(check-sat-using smt)
