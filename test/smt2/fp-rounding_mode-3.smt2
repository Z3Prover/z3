; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_FP)
(set-info :status sat)

(declare-fun rm1 () (RoundingMode))
(declare-fun rm2 () (RoundingMode))

(assert (not (= rm1 rm2)))

(check-sat)
(check-sat-using smt)

