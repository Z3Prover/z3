(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 2) (>= m 2) (>= k 1) (>= l 0) (>= p 2) (>= q 2) (>= r 1) (>= s 0)))
(assert (= (str.++ (seq.power "a" l) (seq.power "c" l)) (str.++ (seq.power (str.++ "a" (seq.power "ba" r) "ab") n) "a")))
(check-sat)
