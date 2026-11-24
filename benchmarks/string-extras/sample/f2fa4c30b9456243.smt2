; origin: https://github.com/plfm-iis/trauc_benchmarks : 08_djangodjango.db.backends.mysql.operationsDatabaseOperations.convert_uuidfield_valueformula2_sat.smt2
(set-logic ALL)
(declare-const self String)
(declare-const value String)
(declare-const expression String)
(declare-const connection String)
(assert (not (< (str.len value) 0)))
(assert (not (= (+ 0 (str.indexof value "urn:" 0)) (- 1))))
(check-sat)




