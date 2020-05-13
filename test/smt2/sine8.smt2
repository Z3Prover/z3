
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)
(declare-const y Real)
(declare-const a Int)
(declare-const b Int)

(simplify (sin (+ x (* 2 pi) y (* 2 (to_real a) pi) (* 2 pi (to_real b)))))
(simplify (sin (+ x (* 2 pi) y (* 6 (to_real a) pi) (* 8 pi (to_real b)))))

