(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 0) (>= m 0) (>= k 1) (>= l 1) (>= p 0) (>= q 1) (>= r 2) (>= s 2)))
(assert (= (seq.power (str.++ (seq.power "ba" p) "bc" "ab") n) (seq.power (str.++ "c" (seq.power "ab" p)) 2)))
(check-sat)
