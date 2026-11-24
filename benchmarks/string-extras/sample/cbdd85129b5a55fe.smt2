(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 0) (>= m 0) (>= k 1) (>= l 1) (>= p 2) (>= q 0) (>= r 0) (>= s 2)))
(assert (= (str.++ (seq.power (str.++ (seq.power "abb" (* 2 q)) (seq.power "ab" p) "ab") n) (seq.power "ba" n) "bc") (seq.power (str.++ (seq.power "abb" p) "b") m)))
(check-sat)
