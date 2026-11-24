(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 2) (>= m 2) (>= k 2) (>= l 0) (>= p 1) (>= q 1) (>= r 0) (>= s 0)))
(assert (= (str.++ (seq.power (str.++ "a" (seq.power "ba" s) "ab") 2) (seq.power (str.++ (seq.power "bc" (+ p 1)) "c") k)) (str.++ (seq.power "c" m) "a")))
(check-sat)
