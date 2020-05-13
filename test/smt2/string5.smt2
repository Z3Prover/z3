; Copyright (c) 2017 Microsoft Corporation
; Github issue #681
(exit)

; seq is unsound. z3str3 diverges

;(set-option :smt.string_solver z3str3)
(set-logic QF_S)
(declare-const a String)
(declare-const c String)
(declare-const A String)
(declare-const C String)
(declare-const ac String)
(declare-const AC String)
(declare-const aacc String)
(declare-const AACC String)
(declare-const aaaccc String)
(declare-const AAACCC String)


(assert (= ac (str.++ a c)))
(assert (= aacc (str.++ a ac c)))
(assert (= aaaccc (str.++ a aacc c)))
(assert (= AC (str.++ A C)))
(assert (= AACC (str.++ A AC C)))
(assert (= AAACCC (str.++ A AACC C)))


(assert (= ac AC))
(assert (= aacc AACC))
(assert (not (= aaaccc AAACCC)))
(check-sat)
(get-model)
