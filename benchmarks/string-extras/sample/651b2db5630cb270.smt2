(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 1) (>= m 1) (>= k 2) (>= l 1) (>= p 0) (>= q 0) (>= r 2) (>= s 2)))
(assert (= (seq.power "bc" 2) (str.++ (seq.power (str.++ (seq.power "ab" (* 2 q)) "ba" "ba") 2) (seq.power (str.++ (seq.power "abb" (+ p 1)) "ba") l))))
(check-sat)
