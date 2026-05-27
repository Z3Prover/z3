; Advanced: Russell's paradox in set theory
(set-logic HO_ALL)
(declare-sort Set 0)
(declare-fun elem () (-> Set Set Bool))
; Russell set: R = {x | x not in x}
(declare-fun R () Set)
(assert (forall ((x Set)) (= (elem x R) (not (elem x x)))))
(check-sat)
(exit)
