; Choice term: definite description
; THE x such that P(x), when P has unique solution
(set-logic HO_ALL)
(declare-fun P () (-> Int Bool))
(assert (exists ((x Int)) (and (P x) (forall ((y Int)) (=> (P y) (= y x))))))
(define-fun the_P () Int (choice ((x Int)) (P x)))
(assert (P 7))
(assert (forall ((x Int)) (=> (P x) (= x 7))))
(assert (not (= the_P 7)))
(check-sat)
(exit)
