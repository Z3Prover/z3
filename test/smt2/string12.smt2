; Copyright (c) 2017 Microsoft Corporation
; issue #731
(set-option :smt.string_solver z3str3)
(declare-fun c0 () Int)
(assert (not (= c0 (str.to.int (int.to.str c0)))))
(check-sat)
(reset)
(set-option :smt.string_solver seq)
(declare-fun c0 () Int)
(assert (not (= c0 (str.to.int (int.to.str c0)))))
(check-sat)
