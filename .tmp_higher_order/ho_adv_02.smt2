; Advanced: Cantor's theorem (no surjection from A to P(A))
(set-logic HO_ALL)
(declare-sort A 0)
(declare-fun f () (-> A (-> A Bool)))
; f is surjective onto P(A)
(assert (forall ((S (-> A Bool))) (exists ((a A)) (= (f a) S))))
; Define the diagonal set
(declare-fun D () (-> A Bool))
(assert (forall ((a A)) (= (D a) (not ((f a) a)))))
; D should have a preimage - contradiction
(check-sat)
(exit)
