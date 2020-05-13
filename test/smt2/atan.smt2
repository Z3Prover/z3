
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)

(simplify (atan (- x)))
(simplify (atan (- 2)))
(simplify (atan 1))
(simplify (atan 0))
(simplify (atan (- 1)))
(simplify (atan (/ 1 2)))
(simplify (atan (* 2 x)))
