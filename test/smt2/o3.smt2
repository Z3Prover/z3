; Copyright (c) 2015 Microsoft Corporation
(declare-const x Int)
(assert (<= x 2))
(maximize x)
(check-sat)
(get-objectives)