; COUNT(1) over UNION ALL becomes the sum of the two partial counts.
(assert (distinct
  (sql.countOne (sql.unionAll (sql.scan "orders") (sql.scan "archive")))
  (sql.addCounts (sql.count (sql.scan "orders")) (sql.count (sql.scan "archive")))))
