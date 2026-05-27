; Choice term: monotonicity of choice
; If P subset Q and both non-empty, choice may differ
(set-logic HO_ALL)
(declare-fun P () (-> Int Bool))
(declare-fun Q () (-> Int Bool))
(assert (forall ((x Int)) (=> (P x) (Q x))))
(assert (exists ((x Int)) (P x)))
(assert (Q (choice ((x Int)) (Q x))))
(assert (P (choice ((x Int)) (P x))))
(check-sat)
(exit)
