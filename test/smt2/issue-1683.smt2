; Copyright (c) 2018 Microsoft Corporation
; GitHub issue

(declare-fun x () Int)
(declare-fun y () Int)

(assert (> x 0))
(assert (> y 0))

; (x * y) / y == x 
(assert (not (= (div (* x y) y) x))) 

(check-sat)

(reset)
(set-option :smt.arith.solver 2)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (> y 0))
(assert (not (= (/   (* x y) y) x)))
(check-sat)

(reset)
(set-option :smt.arith.solver 6)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (> y 0))
(assert (not (= (/   (* x y) y) x)))
(check-sat)
