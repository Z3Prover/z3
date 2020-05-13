
; Copyright (c) 2015 Microsoft Corporation
(declare-const x Int)
(declare-const y Int)
(assert
  (and
   (<= x 0)
   (< 0 y)
   (not 
    (and
     (<= 0 (mod x y))
     (< (mod x y) y)))))
(check-sat)


(reset)

(set-logic QF_NIA)
(set-option :auto-config true)
(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)
(assert
  (and
   (<= x 0)
   (< 0 y)
   (not 
    (and
     (<= 0 (mod x y))
     (< (mod x y) y)))))
(check-sat)

