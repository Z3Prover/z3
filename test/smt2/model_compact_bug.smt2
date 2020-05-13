
; Copyright (c) 2015 Microsoft Corporation
(set-option :model.compact true)
(declare-fun p (Int) Bool)
(assert (p 1))
(assert (p 2))
(assert (p 3))
(check-sat-using smt)
(get-model)