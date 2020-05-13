; Copyright (c) 2017 Microsoft Corporation
; Issuue 949
(set-option :smt.string_solver z3str3)

(declare-const x String)

(assert (not (str.prefixof "prefix:" x)))

(assert (or
         (str.prefixof "prefix:a" x)
         (str.prefixof "prefix:b" x)
         (str.prefixof "prefix:c" x)))
(check-sat)

(reset)
(set-option :smt.string_solver seq)

(declare-const x String)

(assert (not (str.prefixof "prefix:" x)))

(assert (or
         (str.prefixof "prefix:a" x)
         (str.prefixof "prefix:b" x)
         (str.prefixof "prefix:c" x)))
(check-sat)
