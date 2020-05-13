
; Copyright (c) 2015 Microsoft Corporation
(set-option :auto-config true)
(set-option :produce-models true)

; defining my own division operator where x/0.0 == 0.0 for every x.
(define-fun mydiv ((x Real) (y Real)) Real
  (if (not (= y 0.0))
      (/ x y)
      0.0))
(declare-const a Real)
(declare-const b Real)
(assert (>= (mydiv a b) 1.0))
(assert (= b 0.0))
(check-sat)
