
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(declare-const y FPN)
(declare-const z FPN)
(declare-const q FPN)
(declare-const r FPN)
(declare-const m FPN)

(assert (= m (fp.fma roundTowardPositive 
		   ((_ to_fp 11 53) roundNearestTiesToEven 1.24503981037881583660009710001759231090545654296875 (- 757))
		   ((_ to_fp 11 53) roundNearestTiesToEven (- 1.3703055165615218857766421933774836361408233642578125) 73)
		   ((_ to_fp 11 53) roundNearestTiesToEven (- 1.534190900553739300704592096735723316669464111328125) (- 732)))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.24503981037881583660009710001759231090545654296875 (- 757))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven (- 1.3703055165615218857766421933774836361408233642578125) 73)))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven (- 1.534190900553739300704592096735723316669464111328125) (- 732))))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven (- 1.70608492050080773339004736044444143772125244140625) (- 684))))
(assert (= q (fp.fma roundTowardPositive x y z)))
(assert (not (= q r)))

(check-sat)
(check-sat-using smt)
