
; Copyright (c) 2015 Microsoft Corporation
(declare-const x1 Real)
(assert (< (* x1 x1) 0.0))
(check-sat)
