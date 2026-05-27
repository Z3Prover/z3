; HO quantification: Leibniz equality
; Two elements are equal iff they satisfy the same predicates
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(assert (forall ((P (-> U Bool))) (= (P a) (P b))))
(assert (distinct a b))
(check-sat)
(exit)
