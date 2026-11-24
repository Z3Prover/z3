; origin: https://github.com/plfm-iis/trauc_benchmarks : biopython_laterBioSQL.DBUtilsSqlite_dbutils.executemanyformula2_sat.smt2
(set-logic ALL)
(declare-const cursor String)
(declare-const sql String)
(declare-const seq String)
(assert (not (< (str.len sql) 0)))
(assert (not (= (+ 0 (str.indexof sql "%s" 0)) (- 1))))
(check-sat)



