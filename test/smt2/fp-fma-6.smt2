
; Copyright (c) 2015 Microsoft Corporation

;; BUG: mpf != fpu [seed=1365513423, num_tests=99781]
;; sse2 FPU RM (before) : rm-up 
;; sse2 FPU RM (after) : rm-up 
;; Rounding mode: to negative
;; Precision: double (11/53)
;; X = -1.596658482563257930308964205323718488216400146484375p-777 [- 2687110919739334 -777 N] {- 2687110919739334 -777 (-2.00866e-234)}
;; Y = -1.2611088110811881080053353798575699329376220703125p-798 [- 1175929544288392 -798 N] {- 1175929544288392 -798 (-7.56512e-241)}
;; Z = -0 [- 0 -1023 D] {- 0 -1023 (-0)}
;; -1.596658482563257930308964205323718488216400146484375p-777 [- 2687110919739334 -777 N] x -1.2611088110811881080053353798575699329376220703125p-798 [- 1175929544288392 -798 N] -0 [- 0 -1023 D] == -0.0000000000000002220446049250313080847263336181640625p-1022 [- 1 -1023 D]
;;  [HW: +0 [+ 0 -1023 D]] 

;; mpf : - 1 -1023
;; mpfd: - 1 -1023 (-4.94066e-324) class: Neg. denorm.
;; hwf : + 0 -1023 (0) class: +0



(set-logic QF_FP)
(set-info :status unsat)
(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const z FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpfx FPN)

(assert (= mpfx (fp.fma roundTowardNegative
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.596658482563257930308964205323718488216400146484375) (- 777))
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.2611088110811881080053353798575699329376220703125) (- 798))
		  (fp.neg ((_ to_fp 11 53) roundNearestTiesToEven 0.0 0)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven (- 1.596658482563257930308964205323718488216400146484375) (- 777))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven (- 1.2611088110811881080053353798575699329376220703125) (- 798))))
(assert (= z (fp.neg ((_ to_fp 11 53) roundNearestTiesToEven 0.0 0))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 0.0 0)))

(assert (= q (fp.fma roundTowardNegative x y z)))

(assert (not (= q r)))

(check-sat)
(check-sat-using smt)
