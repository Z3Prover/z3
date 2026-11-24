; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/slent_dio_lemma.smt2
; EXPECT: unsat
(set-logic ALL)
(declare-fun x () String)
(assert (= 30 (+ (str.len x) (str.len (str.++ "\u{" (str.replace x ".g" ""))))))
(check-sat)
