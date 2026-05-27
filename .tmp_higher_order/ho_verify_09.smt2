; Verification: frame rule for array operations
(set-logic HO_ALL)
(declare-const arr (Array Int Int))
(declare-const arr2 (Array Int Int))
(define-fun modify_range ((a (Array Int Int)) (lo Int) (hi Int) (f (-> Int Int))) (Array Int Int)
  (lambda ((i Int)) (ite (and (>= i lo) (<= i hi)) (f (select a i)) (select a i))))
(assert (= arr2 (modify_range arr 5 10 (lambda ((x Int)) (+ x 1)))))
; Frame: outside [5,10] is unchanged
(assert (not (= (select arr2 3) (select arr 3))))
(check-sat)
(exit)
