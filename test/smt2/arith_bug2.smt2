
; Copyright (c) 2015 Microsoft Corporation
(set-logic QF_LRA)

(declare-fun v0 () Real)
(declare-fun v1 () Real)

(assert 
 (= (+ (- (/ 1 11)) v0 v1) v0)
)

(check-sat)

(reset)

(set-logic QF_LRA)

(declare-fun v0 () Real)
(declare-fun v1 () Real)

(assert 
 (= (+ 1 v0 v1) v0)
)

(check-sat)
