
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)
(set-info :source "G Paganelli, W Ahrendt: Verifying (In-)Stability in Floating-Point Programs by Increasing Precision, Using SMT Solving. SYNASC 2013.")

(declare-fun g () (_ FloatingPoint 11 53))

(assert (fp.eq
    (( _ to_fp 8 24 ) roundNearestTiesToEven 1.0 2)
    (( _ to_fp 8 24 ) roundNearestTiesToEven 1.0 0)))

(assert (fp.eq ((_ to_fp 11 53) roundNearestTiesToEven 1.0 2) g))

(assert (not (fp.eq g ((_ to_fp 11 53) roundNearestTiesToEven
						( ( _ to_fp 8 24 ) roundNearestTiesToEven 1.0 0)))))

(check-sat)
(check-sat-using smt)
