
; Copyright (c) 2015 Microsoft Corporation

(set-option :pp.decimal true)
(declare-const x Real)
(declare-const y Real)

(simplify (+ (^ 7.0 (/ 2.0 3.0)) (^ 22.0 (/ 3.0 5.0))))
(simplify (^ (+ (^ 7.0 (/ 2.0 3.0)) (^ 22.0 (/ 3.0 5.0))) (/ 1.0 3.0)))

(set-option :pp.decimal-precision 50)
(simplify (^ (+ (^ 7.0 (/ 2.0 3.0)) (^ 22.0 (/ 3.0 5.0))) (/ 1.0 3.0)))
