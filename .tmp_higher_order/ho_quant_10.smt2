; HO quantification: no universal identity
; Not every endofunction is the identity
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (distinct a b))
(assert (forall ((f (-> U U))) (forall ((x U)) (= (f x) x))))
(check-sat)
(exit)
