; Copyright (c) 2015 Microsoft Corporation
(declare-const x Real)
(assert (<= x 2))
(maximize x)
(check-sat)
(get-objectives)