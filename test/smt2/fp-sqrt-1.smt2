
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpf FPN)

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 0.964190623900201604357107498799450695514678955078125 (- 1022))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.9638641744277547385166826643398962914943695068359375 (- 512))))
(assert (= mpf (fp.sqrt roundNearestTiesToEven ((_ to_fp 11 53) roundNearestTiesToEven 0.964190623900201604357107498799450695514678955078125 (- 1022)))))
(assert (= q (fp.sqrt roundNearestTiesToEven x)))
(assert (not (= q r)))

(check-sat)
