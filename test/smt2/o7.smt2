; Copyright (c) 2016 Microsoft Corporation
(declare-const i Int)
(declare-const j Int)

(assert-soft (> i j) :weight 1 )
(assert-soft (< i j) :weight 40.1 )
(check-sat)
(get-objectives)