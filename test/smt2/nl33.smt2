
; Copyright (c) 2015 Microsoft Corporation

(declare-const x Real)
(assert (and
         (< 1.0 x)
         (not (< x (* x x)))))
(check-sat)

(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x Real)
(assert (and
         (< 1.0 x)
         (not (< x (* x x)))))
(check-sat)



