; origin: https://github.com/plfm-iis/trauc_benchmarks : 06_thefucktests.rules.test_npm_wrong_commandtest_matchformula7_sat.smt2
(set-logic ALL)
(declare-const script String)
(assert (not (< (str.len script) 0)))
(assert (str.prefixof "sudo " script))
(assert (not (< (str.len script) 0)))
(assert (not (< (str.len (str.substr script 5 (- (str.len script) 5))) 0)))
(assert (not (= (+ 0 (str.indexof (str.substr script 5 (- (str.len script) 5)) "\u{5c} " 0)) (- 1))))
(check-sat)

