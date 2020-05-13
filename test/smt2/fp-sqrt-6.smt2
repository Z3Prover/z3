
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpfq FPN)

(assert (= mpfq (fp.sqrt roundTowardPositive
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.0983712782233150395683196620666421949863433837890625 823))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.0983712782233150395683196620666421949863433837890625 823)))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.4821412066488910408423862463678233325481414794921875 411)))

(assert (= q (fp.sqrt roundTowardPositive x)))
(assert (not (= q r)))

(check-sat)
