
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const z FPN)
(declare-const q FPN)
(declare-const mpfx FPN)

(assert (= mpfx (fp.fma roundTowardPositive 
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.6890764391177039982494534342549741268157958984375 (- 553))
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.112802390384457940086804228485561907291412353515625) 828)
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.0589641021120208552730446172063238918781280517578125 (- 95)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.6890764391177039982494534342549741268157958984375 (- 553))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven (- 1.112802390384457940086804228485561907291412353515625) 828)))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven 1.0589641021120208552730446172063238918781280517578125 (- 95))))

(assert (= q (fp.fma roundTowardPositive x y z)))
(assert (not (= q mpfx)))

(check-sat)
(check-sat-using smt)
