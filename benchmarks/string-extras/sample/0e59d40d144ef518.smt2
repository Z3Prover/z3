; origin: https://github.com/cvc5/cvc5/tree/main/test/regress/cli : regress0/strings/issue9784.smt2
(set-logic QF_S)
(set-info :status sat)
(declare-const c String)
(assert (not (str.in_re c ((_ re.^ 0) re.all))))
(check-sat)
