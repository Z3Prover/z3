; Copyright Microsoft Corporation 2018
; Unit test of lambda unfolding

(declare-const m (Array Int Int))
(declare-const m1 (Array Int Int))

(define-fun memset ((lo Int) (hi Int) (e Int) (m (Array Int Int))) (Array Int Int)
    (lambda ((x Int)) (if (and (<= lo x) (<= x hi)) e (select m x))))


(declare-const e Int)

(assert (= m1 (memset 5 7 e m)))
(assert (not (= (select m1 6) e)))
(check-sat)
(exit)

