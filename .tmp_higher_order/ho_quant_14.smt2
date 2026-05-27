; HO quantification: functional extensionality
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun f () (-> U U))
(declare-fun g () (-> U U))
(assert (forall ((x U)) (= (f x) (g x))))
(assert (distinct f g))
(check-sat)
(exit)
