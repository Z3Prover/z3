
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

(assert (= m (fp.fma roundNearestTiesToEven 
	       ((_ to_fp 11 53) roundNearestTiesToEven (- 1.064856665573568061944342844071798026561737060546875) (- 138))
	       ((_ to_fp 11 53) roundNearestTiesToEven (- 1.1888181492182809950719502012361772358417510986328125) 238)
	       ((_ to_fp 11 53) roundNearestTiesToEven (- 1.0411411221999600229537463746964931488037109375) 101))))

(assert (= x ((_ to_fp 11 53) roundNearestTiesToEven (- 1.064856665573568061944342844071798026561737060546875) (- 138))))
(assert (= y ((_ to_fp 11 53) roundNearestTiesToEven (- 1.1888181492182809950719502012361772358417510986328125) 238)))
(assert (= z ((_ to_fp 11 53) roundNearestTiesToEven (- 1.0411411221999600229537463746964931488037109375) 101)))

(assert (= q (fp.fma roundNearestTiesToEven x y z)))
(assert (not (= q m)))

(check-sat)
(check-sat-using smt)
