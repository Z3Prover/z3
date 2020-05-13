
; Copyright (c) 2015 Microsoft Corporation
(echo "ACL2 example")
(set-option :auto-config false)
(set-option :produce-models true)
(declare-const x Real)
(declare-const y Real)
(declare-const a Real)
(assert
  (and
   (< (+ (* 3.0 x y) (* 7.0 a)) 4.0)
   (< 3.0 (* 2.0 x))
   (< 1.0 y)
   (not (< a 0.0))
   ))
(check-sat)

(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(set-option :pp.max-depth 100)
(declare-const x Real)
(declare-const y Real)
(declare-const a Real)
(assert
  (and
   (< (+ (* 3.0 x y) (* 7.0 a)) 4.0)
   (< 3.0 (* 2.0 x))
   (< 1.0 y)
   (not (< a 0.0))
   ))
(check-sat)
