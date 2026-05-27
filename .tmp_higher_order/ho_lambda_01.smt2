; Higher-order lambda: constant function
; Based on MBQI-Enum enumeration of simple lambda terms
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (forall ((f (-> U U))) (= (f a) (f b))))
(assert (distinct a b))
(check-sat)
(exit)
