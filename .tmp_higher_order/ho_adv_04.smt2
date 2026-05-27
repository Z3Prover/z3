; Advanced: higher-order unification challenge
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun F () (-> U U))
(declare-fun a () U)
(declare-fun b () U)
; Find F such that F(a) = b and F(b) = a
(assert (= (F a) b))
(assert (= (F b) a))
(assert (distinct a b))
(check-sat)
(get-model)
(exit)
