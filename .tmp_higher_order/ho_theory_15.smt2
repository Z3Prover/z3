; HO + Mixed: higher-order with multiple theories
(set-logic HO_ALL)
(declare-const arr (Array Int (Array Int Int)))
(assert (= arr (lambda ((i Int)) (lambda ((j Int)) (+ i j)))))
(assert (not (= (select (select arr 2) 3) 5)))
(check-sat)
(exit)
