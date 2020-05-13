(set-logic QF_S)
(declare-const x String)
(assert (str.contains (str.++ x "T1WT1t") "GWWT1W"))
(check-sat)
