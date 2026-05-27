; HO + Arrays: array comprehension with guard
(set-logic HO_ALL)
(declare-const a (Array Int Int))
(declare-const b (Array Int Int))
(assert (= a (lambda ((i Int)) i)))
(assert (= b (lambda ((i Int)) (ite (> i 5) (select a i) 0))))
(assert (not (and (= (select b 3) 0) (= (select b 7) 7))))
(check-sat)
(exit)
