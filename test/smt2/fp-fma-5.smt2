
; Copyright (c) 2015 Microsoft Corporation
(set-info :status unsat)
(define-sort FPN () (_ FloatingPoint 11 53))

(declare-const x FPN)
(declare-const y FPN)
(declare-const z FPN)
(declare-const r FPN)
(declare-const q FPN)
(declare-const mpfq FPN)

(assert (= mpfq (fp.fma roundTowardNegative 
		  ((_ to_fp 11 53) roundNearestTiesToEven 1.845689202018911512226395643665455281734466552734375 877)
		  ((_ to_fp 11 53) roundNearestTiesToEven 0.0)
		  ((_ to_fp 11 53) roundNearestTiesToEven (- 1.4759486058585462586734138312749564647674560546875) 108))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven 1.845689202018911512226395643665455281734466552734375 877)))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven 0.0)))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven (- 1.4759486058585462586734138312749564647674560546875) 108)))
(assert (= r ((_ to_fp 11 53) roundNearestTiesToEven (- 1.4759486058585462586734138312749564647674560546875) 108)))
(assert (= q (fp.fma roundTowardNegative x y z)))
(assert (not (= q r)))

(check-sat)
(check-sat-using smt)
