; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : smt2/issue-1224.smt2

(set-option :encoding ascii)
(declare-fun X () String)  
(assert (not (str.in.re X (re.* (re.range "\u{0}" "\u{FF}")))))
(check-sat)

(reset)
(set-option :encoding unicode)
(declare-fun X () String)  
(assert (not (str.in.re X (re.* (re.range "\u{0}" "\u{2FFFF}")))))
(check-sat)
