
; Copyright (c) 2015 Microsoft Corporation
; Rounding mode: to zero
; Precision: double (11/53)
; X = +0.1584131185637904781771112538990564644336700439453125p-1022 {+ 713429261734485 -1023 (3.52481e-309)}
; Y = +1.65717099703655801334889474674127995967864990234375p-22 {+ 2959635057372540 -22 (3.951e-007)}
; +0.1584131185637904781771112538990564644336700439453125p-1022 * +1.65717099703655801334889474674127995967864990234375p-22 == +0.000000062589079252717283452511765062808990478515625p-1022

; mpf : + 281876154 -1023
; mpfd: + 281876154 -1023 (1.39265e-315) class: Pos. denorm.
; hwf : + 281876154 -1023 (1.39265e-315) class: Pos. denorm.

(set-logic QF_FP)
(set-info :status unsat)
(set-option :produce-models true)
(define-sort FPN () (_ FloatingPoint 11 53))

(declare-const x FPN)
(declare-const y FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpfq FPN)

(assert (= mpfq (fp.mul roundTowardZero
		  ((_ to_fp 11 53) roundNearestTiesToEven 0.1584131185637904781771112538990564644336700439453125 (- 1022))
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.65717099703655801334889474674127995967864990234375 (- 22)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 0.1584131185637904781771112538990564644336700439453125 (- 1022))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 1.65717099703655801334889474674127995967864990234375 (- 22))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 0.000000062589079252717283452511765062808990478515625 (- 1022))))
(assert (= q (fp.mul roundTowardZero x y)))

(assert (not (= q r)))
(check-sat)
