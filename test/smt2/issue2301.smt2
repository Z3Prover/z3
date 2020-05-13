(set-option :smt.string_solver z3str3)
(set-info :status sat)
(declare-fun tmp_int2 () Int)
(assert
 (= (str.indexof "" "" tmp_int2) (- 1)))
(check-sat)

(reset)
(set-option :smt.string_solver seq)
(set-info :status sat)
(declare-fun tmp_int2 () Int)
(assert
 (= (str.indexof "" "" tmp_int2) (- 1)))
(check-sat)

