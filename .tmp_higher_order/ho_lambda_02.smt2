; Higher-order lambda: identity instantiation
; MBQI-Enum generates identity lambda as candidate instantiation
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun P ((-> U U)) Bool)
(assert (forall ((f (-> U U))) (P f)))
(assert (not (P (lambda ((x U)) x))))
(check-sat)
(exit)
