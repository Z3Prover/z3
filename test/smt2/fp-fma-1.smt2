
; Copyright (c) 2015 Microsoft Corporation
; Rounding mode: to positive
; Precision: double (11/53)
; X = +1.558866885101854560247147674090228974819183349609375p245 {+ 2516912695494422 245 (8.81369e+073)}
; Y = +1.4875181419808083393974129648995585739612579345703125p-209 {+ 2195586522561125 -209 (1.80798e-063)}
; Z = +0 {+ 0 -1023 (0)}
; +1.558866885101854560247147674090228974819183349609375p245 x +1.4875181419808083393974129648995585739612579345703125p-209 +0 == +1.1594213862610605048075740342028439044952392578125p37
; [HW: +1.1594213862610605048075740342028439044952392578125p37] 

; mpf : + 717970095760200 37
; mpfd: + 717970095760200 37 (1.5935e+011) class: Pos. norm. non-zero
; hwf : + 717970095760200 37 (1.5935e+011) class: Pos. norm. non-zero

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
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.558866885101854560247147674090228974819183349609375 245)
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.4875181419808083393974129648995585739612579345703125 (- 209))
		  ((_ to_fp 11 53) roundNearestTiesToEven 0.0))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.558866885101854560247147674090228974819183349609375 245)))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 1.4875181419808083393974129648995585739612579345703125 (- 209))))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven 0.0)))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.1594213862610605048075740342028439044952392578125 37)))

(assert (= q (fp.fma roundTowardPositive x y z)))
(assert (not (= q r)))

(check-sat)
(check-sat-using smt)
