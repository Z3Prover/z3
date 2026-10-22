(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a () (_ BitVec 3))
(declare-fun b () (_ BitVec 3))
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(declare-fun z () (_ BitVec 2))
(assert (let ((?v_0 (= x y)) (?v_2 (concat (_ bv0 1) x))) (let ((?v_1 (bvadd ?v_2 (concat (_ bv0 1) y)))) (not (and (and (and (= ((_ extract 1 1) (bvnot (concat (_ bv0 1) ((_ extract 3 3) (bvadd (concat (_ bv0 1) a) (concat (_ bv0 1) b)))))) (_ bv1 1)) (=> ?v_0 (= ((_ extract 4 4) ?v_1) ((_ extract 3 3) x)))) (=> ?v_0 (= ?v_1 (bvmul (_ bv2 5) ?v_2)))) (= ((_ extract 3 3) (bvadd (_ bv7 4) (concat (_ bv0 1) (concat z (_ bv1 1))))) (_ bv1 1)))))))
(check-sat)
(exit)
