; Copyright (c) 2017 Microsoft Corporation
; Github issue #912
(exit)
(set-option :smt.string_solver z3str3)
(declare-const s String) 
(declare-const t String) 
(assert (= t (str.replace s "A" "b"))) 
(assert (str.in.re t (re.++ (re.* (re.range "B" "Z")) (str.to.re "A")))) 
(check-sat) 
