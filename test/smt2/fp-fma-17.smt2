
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const z FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpfq FPN)

(assert (= mpfq (fp.fma roundTowardZero 
		  ((_ to_fp 11 53) roundNearestTiesToEven 0.0)
		  ((_ to_fp 11 53) roundNearestTiesToEven 0.0581028354365871191333781098364852368831634521484375 (- 1022))
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.9620335591147675113887771658482961356639862060546875 624))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 0.0)))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 0.0581028354365871191333781098364852368831634521484375 (- 1022))))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven 1.9620335591147675113887771658482961356639862060546875 624)))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.9620335591147675113887771658482961356639862060546875 624)))
(assert (= q (fp.fma roundTowardZero x y z)))
(assert (not (= q r)))

(check-sat)
(check-sat-using smt)
