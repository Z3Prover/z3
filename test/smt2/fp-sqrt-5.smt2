
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpfq FPN)

(assert (= mpfq (fp.sqrt roundTowardNegative
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.1128417976397819710854264485533349215984344482421875 53))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.1128417976397819710854264485533349215984344482421875 53)))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.49187251307863544269594058278016746044158935546875 26)))

(assert (= q (fp.sqrt roundTowardNegative x)))
(assert (not (= q r)))

(check-sat)
