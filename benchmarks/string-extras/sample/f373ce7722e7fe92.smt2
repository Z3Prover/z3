(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 1) (>= m 1) (>= k 1) (>= l 2) (>= p 1) (>= q 1) (>= r 1) (>= s 0)))
(assert (= (seq.power (str.++ "ab" (seq.power "bc" (+ p 1))) 2) (str.++ (seq.power (str.++ "a" (seq.power "bc" r)) 2) (seq.power "a" l))))
(check-sat)
