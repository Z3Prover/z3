
; Copyright (c) 2015 Microsoft Corporation

(set-option :numeral-as-real true)
(declare-const x Real)

(simplify (acos (- 2)))
(simplify (acos 0))
(simplify (acos 1))
(simplify (acos (- 1)))
(simplify (acos (/ 1 2)))
(simplify (acos (- (/ 1 2))))
(simplify (acos x))
(simplify (acos (- x)))