
; Copyright (c) 2015 Microsoft Corporation
; Rounding mode: to zero
; Precision: double (11/53)
; X = -1.5270195366368570777382274172850884497165679931640625p-120 {- 2373484988814721 -120 (-1.1488e-036)}
; Y = -0 {- 0 -1023 (-0)}
; -1.5270195366368570777382274172850884497165679931640625p-120 / -0 == +INF

; mpf : + 0 1024
; mpfd: + 0 1024 (1.#INF) class: +INF
; hwf : + 0 1024 (1.#INF) class: +INF

(set-logic QF_FP)
(set-info :status unsat)
(define-sort FPN () (_ FloatingPoint 11 53))

(declare-const x FPN)
(declare-const y FPN)
(declare-const r FPN) 
(declare-const q FPN) 

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven (- 1.5270195366368570777382274172850884497165679931640625) (- 120))))
(assert (= y (fp.neg ((_ to_fp 11 53) roundNearestTiesToEven 0.0))))
(assert (= r (_ +oo 11 53)))
(assert (= q (fp.div roundTowardZero x y)))
(assert  (not (= q r)))
(check-sat)
(check-sat-using smt)
