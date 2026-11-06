; No theorem permits removing an arbitrary filter.
; SAT is a rewrite-theory model, not a decoded database counterexample.
(assert (distinct
  (sql.filter (sql.lt (sql.column 0) (sql.integer 10)) (sql.scan "orders"))
  (sql.scan "orders")))
