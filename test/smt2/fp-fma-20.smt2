
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

(assert (= m (fp.fma roundTowardZero 
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.1009956705345118610495092070777900516986846923828125) (- 638))
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.507143877086628780403998462134040892124176025390625 (- 579))
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.870475676369866224746374427923001348972320556640625 760))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven (- 1.1009956705345118610495092070777900516986846923828125) (- 638))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 1.507143877086628780403998462134040892124176025390625 (- 579))))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven 1.870475676369866224746374427923001348972320556640625 760)))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven 1.8704756763698660027017695028916932642459869384765625 760)))
(assert (= q (fp.fma roundTowardZero x y z)))
(assert (not (= q r)))

(check-sat)
(check-sat-using smt)
