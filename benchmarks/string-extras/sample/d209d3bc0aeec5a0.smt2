; origin: https://github.com/plfm-iis/trauc_benchmarks : 06_thefucktests.rules.test_grep_arguments_ordertest_get_new_commandformula2_sat.smt2
(set-logic ALL)
(declare-const script String)
(declare-const output String)
(declare-const result String)
(assert (not (< (str.len script) 0)))
(assert (not (= (+ 0 (str.indexof script "\u{5c} " 0)) (- 1))))
(check-sat)



