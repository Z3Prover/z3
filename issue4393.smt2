(set-option :proof true)
(declare-fun a () String)
(assert (= (str.replace "B" (str.replace "" a "A") "") (str.replace "B" a "")))
(check-sat)