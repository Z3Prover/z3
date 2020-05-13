; Copyright (c) 2018 Microsoft Corporation
; GitHub issue

(declare-const x Real)
(assert (is_int x))
(assert (not (is_int (+ x 1))))
(check-sat)