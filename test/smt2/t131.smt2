
; Copyright (c) 2015 Microsoft Corporation
(set-option :smtlib2-compliant true)
(set-logic QF_RDL)

(declare-fun x () Int)
(declare-fun y () Real)
(declare-fun z () (List Int))
(declare-fun w () (Array Int Int))
(declare-fun f (Real) Real)
(declare-fun z () Real)

(assert (>= (* 2 y) 2))
(assert (<= (- y z) 1)) 
(assert (>= y z))
(assert (= y z))
(assert (<= (- z y) 2))
(assert (<= (- (+ z z) (+ y y)) 2))
(assert (<= (- (+ z z z) (+ y y)) 2))
(assert (<= (- (+ z y) (+ y y)) 2))
(assert (or (= y z) (<= y z)))
(assert (distinct y z))
(assert (distinct y (+ 2 z)))
(assert (distinct (- y 3) (+ 2 z)))
(assert (<= (- z y) (/ 2 3)))
(assert (<= (- z y) (/ 2 y)))
(assert (= (* y y) 2))

(declare-fun x () (_ BitVec 32))
(assert (<= (- z y) (- (/ 2 3))))

(assert (<= (- (ite true y (+ y 1)) (ite false z (+ z 2))) (- 3)))

(assert (<= (- z y) (to_real 2)))
