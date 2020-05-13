(declare-fun a () String)
(declare-fun b () String)
(assert (distinct (str.substr (str.++ a "ab" b) 0 (+ (str.len a) 1)) (str.++ a "a")))
(check-sat)