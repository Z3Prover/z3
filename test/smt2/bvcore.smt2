
; Copyright (c) 2015 Microsoft Corporation

(set-logic QF_BV)
(set-option :auto-config true)
(set-option :produce-unsat-cores true)
(assert (! (= (_ bv0 1) (_ bv1 1)) :named a))

(check-sat)
(get-unsat-core)
