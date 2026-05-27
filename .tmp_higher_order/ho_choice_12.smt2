; Choice term: idempotence of choice
(set-logic HO_ALL)
(declare-fun P () (-> Int Bool))
(assert (exists ((x Int)) (P x)))
(assert (not (= (choice ((x Int)) (P x)) (choice ((x Int)) (P x)))))
(check-sat)
(exit)
