(declare-fun a () String)
(assert (distinct (str.prefixof a (str.substr a 1 2)) (= a (str.at a 2))))
(check-sat)
