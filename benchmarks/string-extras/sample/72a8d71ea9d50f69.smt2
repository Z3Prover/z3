; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/re_diff.smt2
; COMMAND-LINE: --lang=smt2.6
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)

(assert (str.in_re x (re.diff (re.* (str.to_re "A")) re.none)))
(assert (or (not (str.in_re x (re.* (str.to_re "A")))) (str.in_re y (re.diff (re.* (str.to_re "B")) re.all))))

(check-sat)
