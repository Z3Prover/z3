
; Copyright (c) 2015 Microsoft Corporation
(declare-const x Real)
(declare-const a Real)
(declare-const b Real)
(assert
  (and
   (< 2.0 x)
   (<= a (+ x b))
   (not (< a (+ (* x x x) b)))
   ))
(check-sat)

(reset)
(set-logic QF_NRA)
(set-option :produce-models true)
(set-option :auto-config true)
(declare-const x Real)
(declare-const a Real)
(declare-const b Real)
(assert
  (and
   (< 2.0 x)
   (<= a (+ x b))
   (not (< a (+ (* x x x) b)))
   ))
(check-sat)
