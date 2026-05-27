; Extensionality: pointwise ordering
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(declare-fun g () (-> Int Int))
(declare-fun h () (-> Int Int))
; f <= g <= h pointwise
(assert (forall ((x Int)) (and (<= (f x) (g x)) (<= (g x) (h x)))))
; but f < h strictly
(assert (exists ((x Int)) (< (f x) (h x))))
(assert (not (exists ((x Int)) (< (f x) (g x)))))
(assert (not (exists ((x Int)) (< (g x) (h x)))))
(check-sat)
(exit)
