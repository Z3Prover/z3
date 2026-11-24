; origin: https://github.com/Z3Prover/z3test/tree/master/regressions : issues/5454.smt2
(set-option :sat.euf true)
(set-option :tactic.default_tactic smt)
(set-option :model_validate true)


(declare-fun RM2 () RoundingMode)
(set-info :status sat)
(assert (= RM2 RM2))
(check-sat)
(reset)


(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(assert
 (forall ((e Real))
  (or (<= c (* a c))
   (and (< 0.0 (/ 2.0 e))
    (=
     (forall ((e Real))
      (not (forall ((e Real)) (< 0.0 d))))
     (=>
      (and (< 0.0 d)
       (forall ((e Real)) (< 0.0 (/ 2.0 e b))))
      (forall ((e Real)) (= a 0.0))))))))
(assert (forall ((f Real)) (> 0.0 (* a c))))
;(check-sat)
(reset)

(set-info :status sat)
(declare-fun a () Int)
(assert (<= (- a a) 0 (div a 0)))
(check-sat)
(reset)




(set-info :status sat)
(set-option :sat.branching.heuristic chb)
(declare-fun A () (Array (_ FloatingPoint 2 3) (_ FloatingPoint 2 2)))
(declare-fun A2 () (Array (_ FloatingPoint 2 3) (_ FloatingPoint 2 2)))
(assert (and (not (= A A2)) (= (select A (_ +oo 2 3)) (select A (_ -oo 2 3)))))
(check-sat)
(reset)

(set-info :status sat)
(declare-fun a_146 () (Array Int Int))
(declare-fun a_98 () (Array Int Int))
(declare-fun a_144 () (Array Int Int))
(assert (and (= a_98 (store a_98 1 0)) (= a_146 (store a_98 0 0)) (not (= a_146 (store a_144 0 0)))))
(check-sat)
(reset)

(set-info :status sat)
(define-funs-rec (
(f () Int)
(pred ((y Int)) Bool)) (
0
(ite (< y 0) false (ite (= y 0) true (pred (- y 2))))
))
(assert (not  (pred 5)))
;(assert (pred 5))
(check-sat)
(reset)


(exit)

(declare-fun p (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (xor (and (<= 0 y) (<= y x)) (p x y))))
(check-sat)
(reset)

(declare-fun symmetric ((Array Int (Array Int Real)) Int) Bool)
(assert (forall ((?n Int) (?a (Array Int (Array Int Real)))) 
   (= (symmetric ?a ?n) (forall ((?i Int) (?j Int)) (or (< 1 ?j) (not (= ?i ?n)) (= (select (?a ?i) ?j) (select (?a ?j) ?i)))))))
(check-sat)

(exit)
(declare-fun y () Int)
(declare-fun c () (Seq Int))
(declare-fun b () (Seq Int))
(assert (forall ((x Int)) (and (= (seq.nth c y) (seq.nth c 0)) (not (= (seq.nth c x) (seq.nth b x))))))
(check-sat)
(reset)
