
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

(assert (= mpfq (fp.fma roundTowardPositive
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.35783445740813579760697393794544041156768798828125) (- 679))
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.5999829398283906822797462154994718730449676513671875) (- 924))
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.98937258286443086063854934764094650745391845703125 (- 872)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven (- 1.35783445740813579760697393794544041156768798828125) (- 679))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven (- 1.5999829398283906822797462154994718730449676513671875) (- 924))))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven 1.98937258286443086063854934764094650745391845703125 (- 872))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.9893725828644310826831542726722545921802520751953125 (- 872))))

(assert (= q (fp.fma roundTowardPositive x y z)))
(assert (not (= q r)))
(check-sat)
(check-sat-using smt)
