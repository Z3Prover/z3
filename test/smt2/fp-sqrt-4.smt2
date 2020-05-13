
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const q FPN)
(declare-const mpfq FPN)
(declare-const r FPN)

(assert (= mpfq (fp.sqrt roundTowardPositive 
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.700489346097645348976357126957736909389495849609375 (- 835)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.700489346097645348976357126957736909389495849609375 (- 835))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.8441742575459867392595469937077723443508148193359375 (- 418))))

(assert (= q (fp.sqrt roundTowardPositive x)))
(assert (not (= q r)))

(check-sat)
