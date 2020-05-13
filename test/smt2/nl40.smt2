
; Copyright (c) 2015 Microsoft Corporation

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert
  (and
   (= (+ (* 11 a) (* 7 b)) 1)
   (= b (+ (* a c) (- 1)))
   (>= c a)
   (= b 0)
   ))
(check-sat)

(reset)

(set-logic QF_NIA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert
  (and
   (= (+ (* 11 a) (* 7 b)) 1)
   (= b (+ (* a c) (- 1)))
   (>= c a)
   (= b 0)
   ))
(check-sat)
