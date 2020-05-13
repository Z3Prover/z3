
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)

(simplify (asin (- x)))
(simplify (asin (- 2)))
(simplify (asin 1))
(simplify (asin 0))
(simplify (asin (- 1)))
(simplify (asin (/ 1 2)))
(simplify (+ pi (asin (- (/ 1 2)))))