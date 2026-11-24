; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/idof-nconst-index.smt2
(set-logic ALL)

(set-info :status sat)
(declare-fun s () String)
(assert (str.contains s "Hello and goodbye!"))
(declare-fun x () Int)
(assert (<= (str.len s) x))
(assert (not (= (str.indexof s "goodbye" (- x 30)) (- 1))))
(check-sat)
