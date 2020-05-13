; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_FP)
(set-info :status sat)

(declare-fun rm () (RoundingMode))

(assert (distinct rm roundNearestTiesToEven))

(check-sat)
(check-sat-using smt)

