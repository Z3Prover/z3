; Advanced: fixpoint characterization
; mu X. F(X) where F is monotone on predicates
(set-logic HO_ALL)
(declare-fun F () (-> (-> Int Bool) (-> Int Bool)))
; F(P)(x) = (x = 0) or (x > 0 and P(x-1))
(assert (forall ((P (-> Int Bool)) (x Int))
  (= ((F P) x) (or (= x 0) (and (> x 0) (P (- x 1)))))))
; lfp(F) should be the naturals predicate
(declare-fun nat () (-> Int Bool))
(assert (forall ((x Int)) (= (nat x) ((F nat) x))))
(assert (not (and (nat 0) (nat 1) (nat 2) (not (nat (- 1))))))
(check-sat)
(exit)
