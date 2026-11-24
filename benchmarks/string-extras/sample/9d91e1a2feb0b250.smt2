; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : indexof-6.smt2
; UNSAT

(set-logic QF_SLIA)

(define-fun y () String "\u{0}\u{0}?#")

(assert (> 0 (str.indexof y "#" 2)))

(check-sat)
(exit)
