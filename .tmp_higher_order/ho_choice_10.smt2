; Choice term: epsilon in quantifier instantiation
; MBQI must find choice term as witness
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun P () (-> U Bool))
(declare-fun Q () (-> U Bool))
(assert (forall ((x U)) (=> (P x) (Q x))))
(assert (P (choice ((x U)) (P x))))
(assert (not (Q (choice ((x U)) (P x)))))
(check-sat)
(exit)
