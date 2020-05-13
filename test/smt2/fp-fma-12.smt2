
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(define-sort FPN () (_ FloatingPoint 11 53))
(declare-const x FPN)
(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.845689202018911512226395643665455281734466552734375 877)))
(declare-const y FPN)
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 0.0)))
(declare-const z FPN)
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven (- 1.4759486058585462586734138312749564647674560546875) 108)))
(declare-const r FPN)
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven (- 1.4759486058585462586734138312749564647674560546875) 108)))

(assert (not (= (fp.fma roundTowardNegative x y z) r)))
(check-sat)
(check-sat-using smt)
