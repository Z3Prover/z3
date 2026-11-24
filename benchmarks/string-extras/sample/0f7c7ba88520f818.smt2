; origin: https://github.com/plfm-iis/trauc_benchmarks : 08_djangodjango.utils.formatssanitize_separatorsformula4_unsat.smt2
(set-logic ALL)
(declare-const value String)
(assert (str.contains value "."))
(assert (not (< (str.len value) 0)))
(assert (not (= (+ 0 (str.indexof value "." 0)) (- 1))))
(assert (< (+ 0 (str.indexof value "." 0)) 0))
(check-sat)

