; Choice term: skolemization equivalent
; exists x. P(x) is equivalent to P(choice x. P(x))
(set-logic HO_ALL)
(declare-fun P () (-> Int Bool))
(assert (exists ((x Int)) (P x)))
(assert (not (P (choice ((x Int)) (P x)))))
(check-sat)
(exit)
