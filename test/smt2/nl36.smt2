
; Copyright (c) 2015 Microsoft Corporation

(declare-const x Int)
(declare-const y Int)
(assert (and
   (<= 0 x)
   (<= (- 1) y)
   (< (+ (* x y) x) 0)
   ))
(check-sat)

(reset)
(set-logic QF_NIA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)
(assert (and
   (<= 0 x)
   (<= (- 1) y)
   (< (+ (* x y) x) 0)
   ))
(check-sat)



