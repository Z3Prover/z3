; HO + Reals: continuous function intermediate value
(set-logic HO_ALL)
(declare-fun f () (-> Real Real))
(assert (< (f 0.0) 0.0))
(assert (> (f 1.0) 0.0))
; For solver: find a point where sign might change
(assert (not (exists ((x Real)) (and (>= x 0.0) (<= x 1.0) (= (f x) 0.0)))))
(check-sat)
(exit)
