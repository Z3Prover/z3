; HO quantification: universal over predicates
(set-logic HO_ALL)
(declare-fun a () Int)
(assert (forall ((P (-> Int Bool))) (=> (P 0) (P a))))
(check-sat)
(get-model)
(exit)
