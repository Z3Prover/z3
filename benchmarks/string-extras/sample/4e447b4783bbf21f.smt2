; origin: https://github.com/plfm-iis/trauc_benchmarks : 06_thefucktests.rules.test_git_pull_uncommitted_changestest_matchformula3_sat.smt2
(set-logic ALL)
(declare-const output String)
(assert (not (str.contains output "trace: alias expansion:")))
(assert (not (str.contains output "You have unstaged changes")))
(assert (str.contains output "contains uncommitted changes"))
(check-sat)

