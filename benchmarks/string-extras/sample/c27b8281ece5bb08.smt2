; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/ctn-decompose-3-sym.smt2
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun w () String)
(declare-fun u () String)
(assert (str.contains x (str.++ y z w)))
(assert (or (not (str.contains x y)) (and (= z u) (not (str.contains x u))) (not (str.contains x w))))
(check-sat)
