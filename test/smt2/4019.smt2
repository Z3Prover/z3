(declare-fun a () String)
(assert (= "" (str.replace "" a "B")))
(check-sat)