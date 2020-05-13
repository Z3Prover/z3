
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)
(assert
  (and
   (<= 0 x)
   (<  y 0)
   (not (and
         (<= (mod x y) 0)
         (< (- 0 y) (mod x y))))
        ))
(check-sat)

(reset)

(set-logic QF_NIA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)
(assert
  (and
   (<= 0 x)
   (<  y 0)
   (not (and
         (<= (mod x y) 0)
         (< (- 0 y) (mod x y))))
        ))
(check-sat)

