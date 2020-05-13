
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const z FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpfx FPN)

(assert (= mpfx ((_ to_fp 11 53) roundNearestTiesToEven 1.829929380787749249037688059615902602672576904296875 (- 427))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven (- 1.6463449040516400234679394998238421976566314697265625) (- 857))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven (- 1.0255047247166533264106647038715891540050506591796875) (- 922))))
(assert (= z (fp.neg ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 11 53) roundNearestTiesToEven 0.0)))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 11 53) roundNearestTiesToEven 0.0))))

(assert (= q (fp.fma roundNearestTiesToEven x y z)))

(assert (not (= q r)))

(check-sat)
(check-sat-using smt)

