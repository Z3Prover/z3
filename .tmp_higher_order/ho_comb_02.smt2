; SKI Combinators: K combinator
(set-logic HO_ALL)
(declare-sort U 0)
(define-fun K ((x U) (y U)) U x)
(declare-fun a () U)
(declare-fun b () U)
(assert (not (= (K a b) a)))
(check-sat)
(exit)
