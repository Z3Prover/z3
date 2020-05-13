; Copyright (c) 2016 Microsoft Corporation
(declare-fun k () Int)
(assert (< (to_real k) 2))
(maximize k)
(check-sat)
(get-objectives)