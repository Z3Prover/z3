(declare-fun s () String)
(assert (distinct (str.suffixof "B" (str.++ s "B")) (= s "")))
(check-sat)