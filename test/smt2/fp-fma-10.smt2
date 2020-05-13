
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const z FPN)
(declare-const q FPN)
(declare-const r FPN)

(declare-const mpfx FPN)
(assert (= mpfx (fp.fma roundNearestTiesToEven 
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.2013761414361407986461927066557109355926513671875 856)
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.0581852198505983242426964352489449083805084228515625 144)
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.7471852551099142925039586771163158118724822998046875) (- 771)))))


(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.2013761414361407986461927066557109355926513671875 856)))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 1.0581852198505983242426964352489449083805084228515625 144)))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven (- 1.7471852551099142925039586771163158118724822998046875) (- 771))))
(assert (= q (fp.fma roundNearestTiesToEven x y z)))
(assert (not (= q mpfx)))

(check-sat)
(check-sat-using smt)
