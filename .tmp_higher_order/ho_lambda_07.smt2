; Higher-order: lambda with array store
(set-logic HO_ALL)
(declare-const arr (Array Int Int))
(declare-const arr2 (Array Int Int))
(assert (= arr2 (lambda ((i Int)) (+ (select arr i) 1))))
(assert (= (select arr 0) 5))
(assert (not (= (select arr2 0) 6)))
(check-sat)
(exit)
