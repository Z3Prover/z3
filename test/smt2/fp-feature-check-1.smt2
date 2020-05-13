
; Copyright (c) 2015 Microsoft Corporation
(set-info :status sat)
(set-info :source "Handcrafted by C.M. Wintersteiger")

(declare-fun RM () RoundingMode)

(assert (or
	  (= RM roundNearestTiesToEven)
	  (= RM roundNearestTiesToAway)
	  (= RM roundTowardPositive)
	  (= RM roundTowardNegative)
	  (= RM roundTowardZero)))

(assert (or
	  (= RM RNE)
	  (= RM RNA)
	  (= RM RTP)
	  (= RM RTN)
	  (= RM RTZ)))

(check-sat)
(check-sat-using smt)
(exit)
