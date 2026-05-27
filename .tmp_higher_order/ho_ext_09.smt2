; Extensionality: function applied to itself
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(declare-fun g () (-> Int Int))
(assert (= f g))
(assert (not (= (f (g 0)) (g (f 0)))))
(check-sat)
(exit)
