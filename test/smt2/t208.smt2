
; Copyright (c) 2015 Microsoft Corporation

(set-option :pp.decimal true)

(simplify (^ 2.0 (/ 1.0 2.0)))
(simplify (^ (^ 2.0 (/ 1.0 2.0)) (/ 1.0 3.0)))

(set-option :pp.decimal-precision 30)
(simplify (^ (^ 2.0 (/ 1.0 2.0)) (/ 1.0 3.0)))

(simplify (^ 5.0 (/ 1.0 3.0)))
