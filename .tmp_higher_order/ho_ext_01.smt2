; Extensionality: function inequality requires witness
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(declare-fun g () (-> Int Int))
(assert (distinct f g))
(assert (not (exists ((x Int)) (distinct (f x) (g x)))))
(check-sat)
(exit)
