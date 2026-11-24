; origin: https://github.com/cdstanford/regex-smt-benchmarks : boolean_and_loops/sat/deadloop1_sat.smt2
(set-logic QF_S)
;---
; .NET regular expressions restricted to 7-bit characters
; membership in
; abcd(bcd)*cd(?(a)b|[0-[0]])|abcdefg
;---
(declare-const x String)
(assert (str.in_re x (re.union (re.++ (re.++ (re.++ (str.to_re "abcd") (re.* (str.to_re "bcd"))) (str.to_re "cd")) (re.inter (str.to_re "a") (str.to_re "b"))) (str.to_re "abcdefg"))))
(check-sat)
;(get-model)
