; Verification: higher-order abstract interpretation
(set-logic HO_ALL)
(declare-fun transfer () (-> (-> Int Bool) (-> Int Bool)))
; transfer preserves truth at 0
(assert (forall ((P (-> Int Bool))) (=> (P 0) ((transfer P) 0))))
; iterating transfer from true everywhere
(declare-fun top () (-> Int Bool))
(assert (forall ((x Int)) (top x)))
(assert (not ((transfer top) 0)))
(check-sat)
(exit)
