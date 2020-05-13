
; Copyright (c) 2015 Microsoft Corporation
(echo "ACL2 example")
(set-option :pp.decimal true)
(set-option :auto-config false)
(set-option :produce-models true)
(declare-const a Real)
(declare-const b Real)
(assert
  (and
   (<= 0.0 a)
   (< a b)
   (not (<= (+ a 1.0) (+ (* a b) b)))
   ))
(check-sat)

(reset)
(set-logic QF_NRA)
(set-option :auto-config true)
(set-option :produce-models true)
(set-option :pp.max-depth 100)
(declare-const a Real)
(declare-const b Real)
(assert
  (and
   (<= 0.0 a)
   (< a b)
   (not (<= (+ a 1.0) (+ (* a b) b)))
   ))
(check-sat)

(reset)
(set-option :auto-config false)
(set-option :produce-models true)
(declare-const a Int)
(declare-const b Int)
(assert
  (and
   (<= 0 a)
   (< a b)
   (not (<= (+ a 1) (+ (* a b) b)))
   ))
(check-sat)

(reset)
(set-logic QF_NIA)
(set-option :auto-config true)
(set-option :produce-models true)
(set-option :pp.max-depth 100)
(declare-const a Int)
(declare-const b Int)
(assert
  (and
   (<= 0 a)
   (< a b)
   (not (<= (+ a 1) (+ (* a b) b)))
   ))
(check-sat)
