; Verification: monotone operator fixed point
(set-logic HO_ALL)
(declare-fun F () (-> (-> Int Bool) (-> Int Bool)))
; F is monotone
(assert (forall ((P (-> Int Bool)) (Q (-> Int Bool)))
  (=> (forall ((x Int)) (=> (P x) (Q x)))
      (forall ((x Int)) (=> ((F P) x) ((F Q) x))))))
; lfp(F) satisfies F(lfp(F)) = lfp(F)
(declare-fun lfp () (-> Int Bool))
(assert (forall ((x Int)) (= (lfp x) ((F lfp) x))))
; lfp is the least
(assert (forall ((P (-> Int Bool)))
  (=> (forall ((x Int)) (=> ((F P) x) (P x)))
      (forall ((x Int)) (=> (lfp x) (P x))))))
(assert (lfp 0))
(assert (not (exists ((P (-> Int Bool))) (and (forall ((x Int)) (=> ((F P) x) (P x))) (not (P 0))))))
(check-sat)
(exit)
