; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : benchmarks/pisa/cvc4/pisa-000.smt2
(set-logic QF_S)
(set-option :produce-models true)


(declare-fun v1 () String)
(declare-fun v2 () String)
(declare-fun v3 () Int)
(declare-fun ret () String)




(assert (= v2 "<") )

(assert (ite (str.contains v1 v2)
             (and (= v3 (str.indexof v1 v2 0)) (= ret (str.substr v1 0 v3)) )
             (= ret v1)
        )
)

(assert (or (str.contains ret "<")  (str.contains ret ">") ) )



(check-sat)
