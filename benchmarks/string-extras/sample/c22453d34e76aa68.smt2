(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 0) (>= m 1) (>= k 2) (>= l 1) (>= p 1) (>= q 1) (>= r 0) (>= s 2)))
(assert (= (seq.power (str.++ "b" "b" (seq.power "abb" p)) l) (seq.power (str.++ (seq.power "abb" r) "ba" (seq.power "bc" (* 2 q))) 2)))
(check-sat)
