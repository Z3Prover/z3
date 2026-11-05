(declare-const a (Array Int Int))
(declare-const i Int)
(assert (not (= (store a i (select a i)) a)))
(check-sat)
