; origin: https://github.com/plfm-iis/trauc_benchmarks : 06_thefucktests.rules.test_yum_invalid_operationtest_get_new_commandformula4_sat.smt2
(set-logic ALL)
(declare-const script String)
(declare-const output String)
(declare-const result String)
(assert (not (< (str.len script) 0)))
(assert (not (str.prefixof "sudo " script)))
(assert (not (< (str.len script) 0)))
(assert (not (= (+ 0 (str.indexof script "\u{5c} " 0)) (- 1))))
(check-sat)



