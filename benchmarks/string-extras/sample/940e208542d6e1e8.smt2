; origin: https://github.com/plfm-iis/trauc_benchmarks : 08_djangodjango.db.backends.oracle.operationsDatabaseOperations.quote_nameformula6_sat.smt2
(set-logic ALL)
(declare-const self String)
(declare-const name String)
(assert (not (< (str.len name) 0)))
(assert (str.prefixof """" name))
(assert (not (< (str.len name) 0)))
(assert (not (= (+ 0 (str.indexof name "%" 0)) (- 1))))
(check-sat)


