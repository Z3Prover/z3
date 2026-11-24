(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 0) (>= m 0) (>= k 2) (>= l 1) (>= p 2) (>= q 0) (>= r 0) (>= s 1)))
(assert (= (str.++ (seq.power "a" m) (seq.power "a" m)) (seq.power (str.++ "b" (seq.power "ab" s)) m)))
(check-sat)
