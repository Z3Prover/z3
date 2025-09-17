(set-info :smt-lib-version 2.0)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun w () Int)

; Complex formula that will create many AST nodes and stress hash table operations
(assert (and
    (> (+ x y) 0)
    (< (- y z) 10)
    (>= (* x z) (+ y w))
    (= (+ x y z w) 100)
    (or (< x 0) (> y 0))
    (and (not (= z 0)) (> w 5))
    (=> (> x 5) (< y 15))
    (ite (> z 10) (< w 20) (> w 30))
    (distinct x y z w)
    (> (+ (* 2 x) (* 3 y) (* 4 z) (* 5 w)) 200)
))

(check-sat)
(exit)