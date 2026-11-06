; The UNION ALL shape is found through the e-class of an opaque query name.
(declare-const input SqlQuery)
(declare-const p SqlPred)
(assert (= input (sql.unionAll (sql.scan "east") (sql.scan "west"))))
(assert (distinct (sql.filter p input)
  (sql.unionAll (sql.filter p (sql.scan "east")) (sql.filter p (sql.scan "west")))))
