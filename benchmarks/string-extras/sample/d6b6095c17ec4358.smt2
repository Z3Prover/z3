; origin: https://github.com/plfm-iis/trauc_benchmarks : 08_djangodjango.db.backends.sqlite3.base_sqlite_datetime_cast_dateformula35_sat.smt2
(set-logic ALL)
(declare-const dt String)
(declare-const tzname String)
(declare-const conn_tzname String)
(assert (not (not (= dt ""))))
(assert (not (not (= conn_tzname ""))))
(assert (not (= tzname conn_tzname)))
(assert (not (< (str.len tzname) 0)))
(assert (not (< (str.len tzname) 0)))
(assert (> (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1) (- 1)))
(assert (not (< (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1) 0)))
(assert (not (< (str.len tzname) 0)))
(assert (not (= (+ 0 (str.indexof tzname (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) (- 1))))
(assert (not (< (+ 0 (str.indexof tzname (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) 0)))
(assert (not (< (+ (+ 0 (str.indexof tzname (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) (str.len (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)))) 0)))
(assert (not (< (str.len tzname) 0)))
(assert (not (< (str.len (str.substr tzname (+ (+ 0 (str.indexof tzname (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) (str.len (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)))) (- (str.len tzname) (+ (+ 0 (str.indexof tzname (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) (str.len (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1))))))) 0)))
(assert (= (+ 0 (str.indexof (str.substr tzname (+ (+ 0 (str.indexof tzname (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) (str.len (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)))) (- (str.len tzname) (+ (+ 0 (str.indexof tzname (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) (str.len (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)))))) (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) (- 1)))
(assert (not (= (str.substr tzname (+ (+ 0 (str.indexof tzname (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) (str.len (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)))) (- (str.len tzname) (+ (+ 0 (str.indexof tzname (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)) 0)) (str.len (str.at tzname (+ (+ (+ 0 (str.indexof tzname "+" 0)) (+ 0 (str.indexof tzname "-" 0))) 1)))))) "")))
(check-sat)



