
; Copyright (c) 2015 Microsoft Corporation
; Rounding mode: nearest, ties to even
; Precision: double (11/53)
; X = +1.5882597688926674006637540514930151402950286865234375p-478 {+ 2649286475982071 -478 (2.03509e-144)}
; Y = +0.617932151031487908454664648161269724369049072265625p-1022 {+ 2782919005125658 -1023 (1.37494e-308)}
; +1.5882597688926674006637540514930151402950286865234375p-478 / +0.617932151031487908454664648161269724369049072265625p-1022 == +1.2851409060375420523314460297115147113800048828125p545

; mpf : + 1284160478178760 545
; mpfd: + 1284160478178760 545 (1.48012e+164) class: Pos. norm. non-zero
; hwf : + 1284160478178760 545 (1.48012e+164) class: Pos. norm. non-zero

(set-logic QF_FP)
(set-info :status unsat)
(set-option :produce-models true)
(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const q FPN)
(declare-const r FPN)
(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.5882597688926674006637540514930151402950286865234375 (- 478))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 0.617932151031487908454664648161269724369049072265625 (- 1022))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.2851409060375420523314460297115147113800048828125 545)))
(assert (= q (fp.div roundNearestTiesToEven x y)))
(assert  (not (= q r)))
(check-sat)
(check-sat-using smt)
