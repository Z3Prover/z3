; origin: https://github.com/uuverifiers/sloth : tests/escapeSequences-1b.smt2
(set-logic QF_S)


(declare-fun x () String)
(declare-fun y () String)

(assert (= x "\u{68}\145\u{6c}l\o"))

;sat
(assert (str.in_re x (re.* (re.range "a" "u"))))
(check-sat)

(check-sat)
