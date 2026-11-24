; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : benchmarks/pisa/abc/pisa-000.smt2
(declare-fun v1 () String)
(declare-fun v2 () String)
(declare-fun v3 () Int)
(declare-fun ret () String)

(assert (= v2 "<") )

(assert (or
          (and (str.contains v1 v2) (= v3 (str.indexof v1 v2 0)) (= ret (str.substr v1 0 v3)) ) 
          (and (not (str.contains v1 v2) )  (= ret v1) )
        )
)

(assert (or (str.contains ret "<")  (str.contains ret ">") ) )

(check-sat)
