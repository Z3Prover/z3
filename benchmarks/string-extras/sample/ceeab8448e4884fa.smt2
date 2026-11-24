; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/issue1684-regex.smt2
(set-info :smt-lib-version 2.6)
(set-logic QF_S)
(set-info :status sat)

(declare-const s String)
(assert (str.in_re s (re.* (re.range "\u{0}" "\u{ff}"))))
(assert (str.in_re s (re.range "\u{0}" "\u{ff}")))
(check-sat)
