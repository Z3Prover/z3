; Names and scalar parameters use Z3's real String and Int theories.
(assert (distinct
  (sql.project (sql.one (sql.column (+ 1 1))) (sql.scan (str.++ "ord" "ers")))
  (sql.project (sql.one (sql.column 2)) (sql.scan "orders"))))
