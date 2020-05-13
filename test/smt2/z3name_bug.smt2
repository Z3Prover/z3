
; Copyright (c) 2015 Microsoft Corporation

(set-option :model.compact true)
(declare-fun p (Int) Bool)
;(declare-fun f (Int Real) Bool)

(assert (p (ite (p 1) 10 20)))
(assert (p 1))
(check-sat-using (then nnf smt))
(get-model)

