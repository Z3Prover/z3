
; Copyright (c) 2015 Microsoft Corporation
; Rounding mode: to positive
; Precision: double (11/53)
; X = -0.090632996968847745478115029982291162014007568359375p-1022 {- 408174731376374 -1023 (-2.01665e-309)}
; Y = +0.256038495795966269952259608544409275054931640625p-1022 {+ 1153094874259216 -1023 (5.69705e-309)}
; -0.090632996968847745478115029982291162014007568359375p-1022 + +0.256038495795966269952259608544409275054931640625p-1022 == +0.165405498827118524474144578562118113040924072265625p-1022

; mpf : + 744920142882842 -1023
; mpfd: + 744920142882842 -1023 (3.68039e-309) class: Pos. denorm.
; hwf : + 744920142882842 -1023 (3.68039e-309) class: Pos. denorm.

(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpfx FPN)

(assert (= mpfx (fp.add roundTowardPositive
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 0.090632996968847745478115029982291162014007568359375) (- 1022))
		  ((_ to_fp 11 53) roundNearestTiesToEven 0.256038495795966269952259608544409275054931640625 (- 1022)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven (- 0.090632996968847745478115029982291162014007568359375) (- 1022))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 0.256038495795966269952259608544409275054931640625 (- 1022))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 0.165405498827118524474144578562118113040924072265625 (- 1022))))
(assert (= q (fp.add roundTowardPositive x y)))
(assert (not (= q r)))

(check-sat)
(check-sat-using smt)
