(declare-const n Int)(declare-const m Int)(declare-const k Int)(declare-const l Int)(declare-const p Int)(declare-const q Int)(declare-const r Int)(declare-const s Int)
(assert (and (>= n 1) (>= m 0) (>= k 0) (>= l 0) (>= p 1) (>= q 0) (>= r 1) (>= s 1)))
(assert (= (str.++ (seq.power (str.++ (seq.power "abb" (* 2 q)) "ab") l) (seq.power "ab" m)) (seq.power (str.++ (seq.power "abb" p) "bc") l)))
(check-sat)
