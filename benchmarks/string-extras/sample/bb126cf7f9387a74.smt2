(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 1) (>= m 2) (>= k 0) (>= l 2) (>= p 0) (>= q 1) (>= r 1) (>= s 2)))
(assert (= (str.++ (seq.power (str.++ "b" (seq.power "ab" s)) m) (seq.power (str.++ "ba" "bc" (seq.power "ba" (* 2 q))) n)) (seq.power (str.++ (seq.power "ab" q) "bc" "ab") n)))
(check-sat)
