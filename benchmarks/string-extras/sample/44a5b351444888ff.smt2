; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/dd.instance51542.smt2
; EXPECT: unsat
(set-logic ALL)
(declare-const X String)
(assert (str.in_re X (re.++ (str.to_re "\u{5c}") ((_ re.loop 45 45) (re.* (str.to_re "2"))))))
(assert (not (str.in_re X (re.++ (str.to_re "\u{5c}") re.all))))
(check-sat)
