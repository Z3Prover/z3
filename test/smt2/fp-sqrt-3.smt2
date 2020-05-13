
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))

(declare-const x FPN)
(declare-const q FPN)
(declare-const r FPN)
(declare-const mpfq FPN)

(assert (= mpfq (fp.sqrt roundNearestTiesToEven 
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.114412970334050623222310605342499911785125732421875 (- 149)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.114412970334050623222310605342499911785125732421875 (- 149))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.492925296412416447111581874196417629718780517578125 (- 75))))

(assert (= q (fp.sqrt roundNearestTiesToEven x)))
(assert (not (= q r)))

(check-sat)
