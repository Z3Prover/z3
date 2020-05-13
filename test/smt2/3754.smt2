(set-option :trace true)
(declare-fun a () Float32)
(assert (= a ((_ to_fp 8 24) roundTowardZero a)))
(check-sat-using lra)