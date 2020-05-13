
; Copyright (c) 2015 Microsoft Corporation



(simplify (root-obj 0 1))
(simplify (root-obj 1 1))
(simplify (root-obj x 2))
(simplify (root-obj x 1))
(simplify (root-obj (+ (* 2 x) 1) 1))
(simplify (root-obj (+ (* 2 x) 1) 2))
(simplify (root-obj (- (^ x 5) x 1) 1))
(set-option :pp.decimal true)
(simplify (root-obj (- (^ x 5) x 1) 1))
(simplify (root-obj (^ x 2) 1))
(simplify (root-obj (+ (^ x 2) 2)) 1)
(simplify (root-obj (+ (^ x 2) 2) 1))
(simplify (root-obj (+ (^ x 2) (- 2)) 1))
(simplify (root-obj (+ (^ x 2) (- 2)) 2))
(simplify (root-obj (+ (* 3 (^ x 2)) (- 2)) 2))
(set-option :pp.decimal false)
(simplify (root-obj (+ (* 3 (^ x 2)) (- 2)) 2))
(simplify (root-obj (+ (^ x 5) (* (- 1) x) (- 1)) 1))

