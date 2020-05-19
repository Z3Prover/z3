(declare-const a String)
(assert (xor (distinct a "01") (> (str.to.int a) (- 2))))
(check-sat)