
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_FP)
(set-info :status unsat)

(push)

(declare-fun rm1 () (RoundingMode))
(declare-fun rm2 () (RoundingMode))
(declare-fun rm3 () (RoundingMode))
(declare-fun rm4 () (RoundingMode))
(declare-fun rm5 () (RoundingMode))

(assert (and (= rm1 roundNearestTiesToEven) (not (= rm1 RNE))))
(assert (and (= rm2 roundNearestTiesToAway) (not (= rm2 RNA))))
(assert (and (= rm3 roundTowardPositive) (not (= rm3 RTP))))
(assert (and (= rm4 roundTowardNegative) (not (= rm4 RTN))))
(assert (and (= rm5 roundTowardZero) (not (= rm5 RTZ))))

(check-sat)
(check-sat-using smt)
 
