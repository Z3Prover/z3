(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 2) (>= m 1) (>= k 1) (>= l 0) (>= p 1) (>= q 1) (>= r 0) (>= s 1)))
(assert (= (seq.power (str.++ "c" (seq.power "ba" r) "a") l) (seq.power (str.++ "c" "bc" (seq.power "b" q)) l)))
(check-sat)
