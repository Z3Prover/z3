(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 1) (>= m 1) (>= k 2) (>= l 1) (>= p 0) (>= q 1) (>= r 2) (>= s 1)))
(assert (= (str.++ (seq.power "c" k) (seq.power (str.++ (seq.power "b" (* 2 q)) "b") n) "bc") (seq.power "a" 2)))
(check-sat)
