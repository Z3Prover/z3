
; Copyright (c) 2015 Microsoft Corporation


(declare-datatypes () ((T A B)))
(assert ((_ is A) A))
(assert ((_ is B) B))
(check-sat)
