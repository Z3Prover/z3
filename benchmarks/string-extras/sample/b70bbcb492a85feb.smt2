; origin: https://github.com/vlab-cs-ucsb/ABC/tree/master/test : benchmarks/pisa/cvc4/pisa-009.smt2
(set-logic QF_S)
(set-option :produce-models true)


(declare-fun s () String)
(declare-fun ret0 () String)
(declare-fun ret1 () String)

(assert (= ret0 (str.replace (str.replace  s  "<"  "&lt;")  ">"  "&gt;") ) )

(assert (= ret1 (str.++  ret0  "<br/>") ) )

(assert (or (str.contains ret1 "<") (str.contains ret1 ">") ) )

(check-sat)

