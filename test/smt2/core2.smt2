
; Copyright (c) 2015 Microsoft Corporation

(set-option :produce-unsat-cores true)

(declare-const a Bool)
(assert (or (not a) (= 1 0)))
(check-sat a)
(get-unsat-core)