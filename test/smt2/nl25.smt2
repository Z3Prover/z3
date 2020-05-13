
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert
  (and
      (< (+ (* x1 x1) (* (- 2.0) x1 x2) (* x2 x2)) x3)
      (< x3 0.0)
   ))
(check-sat)

(exit)
;; the same example is much slower with AUTO_CONFIG=true

(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const x3 Real)
(assert
  (and
      (< (+ (* x1 x1) (* (- 2.0) x1 x2) (* x2 x2)) x3)
      (< x3 0.0)
   ))
(check-sat)



