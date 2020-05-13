
; Copyright (c) 2015 Microsoft Corporation
;; sse2 FPU RM (before) : rm-down
;; sse2 FPU RM (after) : rm-up
;; Rounding mode: to positive
;; Precision: double (11/53)
;; X = -0.5792861143265499723753464422770775854587554931640625p-1022 {- 2608872728621953 -1023 (-1.28895e-308)}
;; Y = -1.3902774452208657152141313417814671993255615234375p-17 {- 1757653356867800 -17 (-1.0607e-005)}
;; -0.5792861143265499723753464422770775854587554931640625p-1022 * -1.3902774452208657152141313417814671993255615234375p-17
;;  == +0.000006144473412295070602340274490416049957275390625p-1022

;; mpf : + 27672248170 -1023
;; mpfd: + 27672248170 -1023 (1.36719e-313) class: Pos. denorm.
;; hwf : + 27672248170 -1023 (1.36719e-313) class: Pos. denorm.


(set-logic QF_FP)
(set-info :status unsat)
(set-option :produce-models true)
(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpfx FPN)

(assert (= mpfx (fp.mul roundTowardPositive
		  ((_ to_fp 11 53) roundNearestTiesToEven 0.5792861143265499723753464422770775854587554931640625 (- 1022))
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.3902774452208657152141313417814671993255615234375 (- 17)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 0.5792861143265499723753464422770775854587554931640625 (- 1022))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 1.3902774452208657152141313417814671993255615234375 (- 17))))

(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 0.000006144473412295070602340274490416049957275390625 (- 1022))))
(assert (= q (fp.mul roundTowardPositive x y)))

(assert  (not (= q r)))
(check-sat)
