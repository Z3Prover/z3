;(set-info :status sat)
(declare-const S String)
(declare-const T String)
(assert (= S "\u{5c}"))
(assert (= (str.len S) 1))

(assert (= T "\u{0a}"))
(assert (= (str.len T) 1))

(check-sat)
(get-model)
