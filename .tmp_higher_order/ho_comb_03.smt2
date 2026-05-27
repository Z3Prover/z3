; SKI Combinators: I = SKK
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun a () U)
(define-fun K ((x U) (y U)) U x)
(define-fun S_comb ((f (-> U U U)) (g (-> U U)) (x U)) U (f x (g x)))
; S K K x = K x (K x) = x
(assert (not (= (S_comb (lambda ((x U) (y U)) (K x y))
                   (lambda ((x U)) (K x a))
                   a)
               a)))
(check-sat)
(exit)
