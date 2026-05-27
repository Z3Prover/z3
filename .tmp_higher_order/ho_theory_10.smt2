; HO + Sets: set comprehension via lambda
(set-logic HO_ALL)
(declare-const S (Array Int Bool))
(assert (= S (lambda ((x Int)) (and (>= x 0) (< x 10)))))
(assert (not (select S 5)))
(check-sat)
(exit)
