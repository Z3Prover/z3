
; Copyright (c) 2015 Microsoft Corporation


(simplify (^ (/ 1.0 27.0) (/ 1.0 3.0)))
(simplify (^ (/ 1.0 27.0) (- (/ 1.0 3.0))))
(simplify (^ (/ 1.0 27.0) (- (/ 2.0 3.0))))
(simplify (^ (/ 64.0 27.0) (/ 1.0 3.0)))
(simplify (^ (/ 64.0 27.0) (/ 2.0 3.0)))
(simplify (^ (/ 64.0 27.0) (- (/ 1.0 3.0))))
(simplify (^ (/ 64.0 27.0) (- (/ 2.0 3.0))))
(simplify (^ 3 2))
(simplify (^ 0 0))

(declare-const x Int)
(declare-const y Real)

(simplify (^ 1 x))
(simplify (^ x 0))
(simplify (^ 1.0 y))
(simplify (^ 0 x))
(simplify (^ 0.0 y))
(simplify (^ x 1))
(simplify (^ y 1.0))
(simplify (^ 0.0 0.0))
(simplify (^ 2 64))
(simplify (^ 2 65))
(simplify (^ 2 65)
          :max-degree 100)
(simplify (^ 2 (- 3)))
(simplify (^ 2.0 (- 3.0)))
