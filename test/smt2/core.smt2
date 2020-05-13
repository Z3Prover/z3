
; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_LRA)
(set-option :auto-config true)
(set-option :produce-unsat-cores true)

(assert (! (= 1 0) :named a))

(check-sat)
(get-unsat-core)