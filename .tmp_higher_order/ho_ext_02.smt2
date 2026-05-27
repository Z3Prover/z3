; Extensionality: congruence for HO application
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(declare-fun g () (-> Int Int))
(declare-fun a () Int)
(assert (= f g))
(assert (not (= (f a) (g a))))
(check-sat)
(exit)
