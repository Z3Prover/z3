
; Copyright (c) 2015 Microsoft Corporation
(set-option :produce-models true)
(set-info :source "Handcrafted; from Z3 GitHub issue 222.")
(set-info :status sat)

(set-logic QF_FP)
(declare-fun x () Float32)

(assert (= (fp.sqrt RNE x) (fp.sqrt RNE (fp #b0 #b00000000 #b00000000000000000000001))))
(check-sat)
(get-value (x))
(exit)
