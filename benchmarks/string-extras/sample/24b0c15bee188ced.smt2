; origin: https://github.com/uuverifiers/sloth : tests/escapeSequences-1a.smt2
(set-logic QF_S)


(declare-fun x () String)
(declare-fun y () String)

(assert (= x "\u{48}\145\u{6c}l\o"))

;unsat
(assert (str.in_re x (re.* (re.range "a" "u"))))
(check-sat)

(check-sat)
