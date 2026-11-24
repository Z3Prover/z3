; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/type002.smt2
(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(set-info :status sat)


(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun i () Int)

(assert (>= i 420))
(assert (= x (str.from_int i)))
(assert (= x (str.++ y "0" z)))
(assert (not (= y "")))
(assert (not (= z "")))



(check-sat)
