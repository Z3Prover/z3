(set-option :smt.string_solver z3str3)
(assert (forall ((a (_ BitVec 2)))
  (exists ((b (_ BitVec 2))) (and (= a #b00) (distinct a b)))))
(check-sat-using qe)