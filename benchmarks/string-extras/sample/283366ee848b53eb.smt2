; origin: https://github.com/uuverifiers/ostrich/tree/master/tests : all-quantifiers.smt2
; Problem for which Ostrich previously return sat.
; The formula is actually unsat.

(set-logic ALL)
(assert
  (forall ((char String))
    (=> (str.contains char ":")
        (str.contains char "://"))))
(check-sat)