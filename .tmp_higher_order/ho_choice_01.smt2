; Choice term: basic witness
; Hilbert choice: (choice ((x T)) phi) denotes some x satisfying phi
(set-logic HO_ALL)
(declare-sort U 0)
(declare-fun P () (-> U Bool))
(assert (exists ((x U)) (P x)))
(declare-fun witness () U)
(assert (= witness (choice ((x U)) (P x))))
(assert (not (P witness)))
(check-sat)
(exit)
