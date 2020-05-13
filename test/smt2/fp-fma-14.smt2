
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
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.1216495060267686056931779603473842144012451171875 (- 540))
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.4169129833028837328612326018628664314746856689453125) 994)
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.234509419381781381019891341566108167171478271484375 481))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.1216495060267686056931779603473842144012451171875 (- 540))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven (- 1.4169129833028837328612326018628664314746856689453125) 994)))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven 1.234509419381781381019891341566108167171478271484375 481)))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.234509407540724357232875263434834778308868408203125 481)))
(assert (= q (fp.fma roundTowardZero x y z)))
(assert (not (= q r)))

(check-sat)
(check-sat-using smt)
