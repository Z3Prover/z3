; Choice term: unique choice
(set-logic HO_ALL)
(declare-fun P () (-> Int Bool))
(assert (P 42))
(assert (forall ((x Int)) (=> (P x) (= x 42))))
(assert (not (= (choice ((x Int)) (P x)) 42)))
(check-sat)
(exit)
