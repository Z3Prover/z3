; HO + Arrays: array defined by lambda
(set-logic HO_ALL)
(declare-const a (Array Int Int))
(assert (= a (lambda ((i Int)) (* i i))))
(assert (not (= (select a 5) 25)))
(check-sat)
(exit)
