
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
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.51795151993714316773775863111950457096099853515625) (- 752))
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.062072095982947939063478770549409091472625732421875) 313)
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.5859600563433839948146442111465148627758026123046875) (- 439)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven (- 1.51795151993714316773775863111950457096099853515625) (- 752))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven (- 1.062072095982947939063478770549409091472625732421875) 313)))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven (- 1.5859600563433839948146442111465148627758026123046875) (- 439))))
(assert (= q (fp.fma roundTowardPositive x y z)))

(assert (not (= q mpfx)))

(check-sat)
(check-sat-using smt)
