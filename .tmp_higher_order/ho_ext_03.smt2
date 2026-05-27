; Extensionality: eta-equivalence
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(declare-fun g () (-> Int Int))
(assert (= g (lambda ((x Int)) (f x))))
(assert (distinct f g))
(check-sat)
(exit)
