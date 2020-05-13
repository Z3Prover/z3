
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
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.23310370494159737830841550021432340145111083984375 (- 782))
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.95921676596909311030003664200194180011749267578125 257)
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 0.23041672199193641290548839606344699859619140625) (- 1022)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.23310370494159737830841550021432340145111083984375 (- 782))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 1.95921676596909311030003664200194180011749267578125 257)))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven (- 0.23041672199193641290548839606344699859619140625) (- 1022))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.2079587264500915022580329605261795222759246826171875 (- 524))))

(assert (= q (fp.fma roundTowardZero x y z)))
(assert (not (= q r)))

(check-sat)
(check-sat-using smt)
