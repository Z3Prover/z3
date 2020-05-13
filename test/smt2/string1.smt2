; Copyright (c) 2017 Microsoft Corporation
(set-option :smt.string_solver z3str3)
(declare-const a String)
(set-option :model_validate true)
(set-info :status sat)
(assert (= "ab" (str.replace a "yyy" "abb")))
;(check-sat)
;(get-model)
