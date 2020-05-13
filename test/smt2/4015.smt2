(declare-fun a () String)
(declare-fun b () String)
(assert (distinct (str.contains (str.replace "B" a b) b) (str.prefixof a (str.replace "" b a))))
(check-sat)