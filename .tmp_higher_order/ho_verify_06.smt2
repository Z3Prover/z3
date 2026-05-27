; Verification: callback safety
(set-logic HO_ALL)
(declare-fun callback () (-> Int Int))
(declare-fun safe () (-> Int Bool))
(assert (= safe (lambda ((x Int)) (and (>= x 0) (<= x 100)))))
; callback preserves safety
(assert (forall ((x Int)) (=> (safe x) (safe (callback x)))))
(assert (safe 50))
(assert (not (safe (callback (callback 50)))))
(check-sat)
(exit)
