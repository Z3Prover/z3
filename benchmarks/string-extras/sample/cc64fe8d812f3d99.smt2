; origin: https://github.com/plfm-iis/trauc_benchmarks : 08_djangodjango.db.backends.sqlite3.base_sqlite_date_truncformula5_unsat.smt2
(set-logic ALL)
(declare-const lookup_type String)
(declare-const dt String)
(declare-const tzname String)
(declare-const conn_tzname String)
(assert (not (= dt "")))
(assert (not (str.contains dt " ")))
(assert (not (not (= dt ""))))
(check-sat)




