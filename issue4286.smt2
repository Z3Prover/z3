(set-option :smt.string_solver z3str3)
(declare-const i9 Int)
(assert (>= (str.len (int.to.str i9)) 285))
(check-sat-using ctx-solver-simplify)