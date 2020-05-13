(declare-const x Int)
(declare-const y Int)
(assert (forall ((Q (Array Int Bool))) (=> (select Q x) (select Q y))))
(assert (not (= x y)))
(check-sat)

