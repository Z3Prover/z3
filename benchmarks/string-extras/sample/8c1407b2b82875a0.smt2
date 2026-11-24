; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/seq-ex5.smt2
(set-logic ALL)

(set-info :status sat)
(declare-fun z () (Seq Int))
(declare-fun w () (Seq Int))
(declare-fun i () Int)
(assert (> i 777))
(assert (not (= (seq.replace z (seq.unit i) w) z)))
(check-sat)
