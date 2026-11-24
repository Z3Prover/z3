; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress1/strings/re-agg-total2.smt2
; REQUIRES: no-safe-mode
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(set-info :status unsat)

(declare-const x String)
(declare-const y String)
(assert (str.in_re x (re.* (str.to_re "'\r''k'\n'"))))
(assert (str.in_re x (re.* (str.to_re "'\r''k'\n''\r''k'\n'"))))
(assert (> (str.len x) 20))
(assert (< (str.len x) 25))
(check-sat)
