; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/seq/seq-nemp.smt2
(set-logic ALL)
(set-info :status sat)
(declare-fun x () (Seq Int))
(assert (not (= x (as seq.empty (Seq Int)))))
(assert (= (seq.len x) 16))
(check-sat)
