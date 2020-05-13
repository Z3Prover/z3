
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 0.6871903324552552927428905604756437242031097412109375 (- 1022))))
(declare-const y FPN)
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven (- 0.495118165444655033979870495386421680450439453125) (- 1022))))
(declare-const r FPN)
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.1823084978999103267227610558620654046535491943359375 (- 1022))))
(assert (not (= (fp.sub roundTowardZero x y) r)))

(check-sat)
(check-sat-using smt)
