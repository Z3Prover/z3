; SKI Combinators: S combinator
(set-logic HO_ALL)
(declare-sort U 0)
(define-fun S ((f (-> U U U)) (g (-> U U)) (x U)) U
  (f x (g x)))
(declare-fun f () (-> U U U))
(declare-fun g () (-> U U))
(declare-fun a () U)
(assert (not (= (S f g a) (f a (g a)))))
(check-sat)
(exit)
