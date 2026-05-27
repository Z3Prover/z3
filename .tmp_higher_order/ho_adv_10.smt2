; Advanced: higher-order resolution challenge
; Requires higher-order unification to refute
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun P () (-> (-> U U) Bool))
(declare-fun a () U)
(declare-fun b () U)
(assert (distinct a b))
(assert (P (lambda ((x U)) a)))
(assert (P (lambda ((x U)) b)))
(assert (forall ((F (-> U U))) (=> (P F) (= (F a) (F b)))))
(check-sat)
(exit)
