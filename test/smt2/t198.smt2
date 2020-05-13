
; Copyright (c) 2015 Microsoft Corporation


(declare-datatypes () ((T A B)))
(declare-const x T)
(assert ((_ is A) x))
(assert ((_ is B) x))
(check-sat)
