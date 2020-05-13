
; Copyright (c) 2015 Microsoft Corporation

(set-option :pp.decimal true)
(declare-const x Real)
(declare-const y Real)

(simplify (/ 1.0 (^ 2.0 (/ 1.0 2.0))))
(simplify (/ 3.0 (^ 2.0 (/ 1.0 2.0))))
(simplify (/ (^ 2.0 (/ 1.0 2.0)) 3.0))
(simplify (= (/ 1.0 (^ 2.0 (/ 1.0 2.0)))
             (/ (^ 2.0 (/ 1.0 2.0)) 2.0)))
(simplify (/ (^ 2.0 (/ 1.0 2.0)) (^ 3.0 (/ 1.0 2.0))))
(simplify (/ (^ 2.0 (/ 1.0 2.0)) 0.0))
(simplify (/ (^ 2.0 (/ 1.0 2.0)) 1.0))



