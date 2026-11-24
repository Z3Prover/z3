; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/regexp001.smt2
(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :status sat)


(declare-fun x () String)

(assert (str.in_re x
		(re.* (re.++ (re.* (str.to_re "a") ) (str.to_re "b") ))
	))

(assert (= (str.len x) 3))

(check-sat)
