; Source: uuverifiers/princess - testcases/arrays/lambda.smt2
; Lambda used to define memset over arrays

(declare-const m (Array Int Int))
(declare-const m1 (Array Int Int))
(declare-const z Int)
(define-fun memset ((lo Int) (hi Int) (y Int) (m (Array Int Int))) 
                   (Array Int Int) 
           (lambda ((x Int)) (ite (and (<= lo x) (<= x hi)) y (select m x))))
(assert (= m1 (memset 1 700 z m)))
(assert (not (= (select m1 6) z)))
(check-sat)
