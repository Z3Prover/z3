; Copyright (c) 2015 Microsoft Corporation
(declare-const x Int)
(declare-const y Int)
(assert (<= x y))
(assert (<= y 5))
(maximize x)
(check-sat)
(get-objectives)