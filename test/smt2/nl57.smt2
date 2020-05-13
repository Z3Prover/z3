
; Copyright (c) 2015 Microsoft Corporation
(declare-const x Real)
(declare-const y Real)
(assert 
  (and
   (<= 0.0 x)
   (<= (- 1.0) y)
   (< (+ (* x y) x) 0.0)
))
(check-sat)

(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x Real)
(declare-const y Real)
(assert 
  (and
   (<= 0.0 x)
   (<= (- 1.0) y)
   (< (+ (* x y) x) 0.0)
))
(check-sat)
