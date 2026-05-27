; Extensionality: function space is not well-ordered
; There exist incomparable functions
(set-logic HO_ALL)
(declare-fun f () (-> Int Int))
(declare-fun g () (-> Int Int))
(assert (exists ((x Int)) (> (f x) (g x))))
(assert (exists ((x Int)) (< (f x) (g x))))
(check-sat)
(get-model)
(exit)
