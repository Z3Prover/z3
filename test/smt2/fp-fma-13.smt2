
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)
(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const z FPN)
(declare-const q FPN)
(declare-const r FPN)
(declare-const mpfq FPN)

(assert (= mpfq  (fp.fma roundTowardZero 
		   ((_ to_fp 11 53) roundNearestTiesToEven (- 1.6168876510806649005047574974014423787593841552734375) (- 152))
		   ((_ to_fp 11 53) roundNearestTiesToEven 1.130656930486356515075385686941444873809814453125 195)
		   ((_ to_fp 11 53) roundNearestTiesToEven 1.2956482502699080416874721777276135981082916259765625 548))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven (- 1.6168876510806649005047574974014423787593841552734375) (- 152))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 1.130656930486356515075385686941444873809814453125 195)))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven 1.2956482502699080416874721777276135981082916259765625 548)))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.2956482502699078196428672526963055133819580078125 548)))

(assert (= q (fp.fma roundTowardZero x y z)))
(assert (not (= q r)))
(check-sat)
(check-sat-using smt)
