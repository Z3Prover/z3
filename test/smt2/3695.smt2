(set-option :smt.threads 2)
;(set-option :smt.random_seed 2)
(declare-fun a () (Set (_ BitVec 1)))
(declare-fun b () (Set (_ BitVec 1)))
(declare-fun c () (Set (_ BitVec 1)))
(declare-fun d () (Set (_ BitVec 1)))
(declare-fun e () (Set (_ BitVec 1)))
;(assert (distinct a b c d))
(assert (not (= a b)))
(assert (not (= a c)))
(assert (not (= a d)))
(assert (not (= b c)))
(assert (not (= b d)))
(assert (not (= c d)))
(assert (not (= e a)))
(assert (not (= e b)))
(assert (not (= e c)))
(assert (distinct e d))
(check-sat)