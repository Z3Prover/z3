(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun argv_1 () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun packet () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (concat (concat (concat (select argv_1 (_ bv6 32)) (select argv_1 (_ bv5 32))) (select argv_1 (_ bv4 32))) (select argv_1 (_ bv3 32))) (_ bv0 32)))
(assert (= (concat (_ bv0 24) (select packet (_ bv240 32))) (_ bv53 32)))
(assert (not (not (= (concat (_ bv0 24) (_ bv0 8)) (concat (_ bv0 24) (select packet (_ bv28 32)))))))
(assert (not (not (= (concat (_ bv0 24) (_ bv0 8)) (concat (_ bv0 24) (select packet (_ bv29 32)))))))
(assert (not (= (concat (_ bv0 24) (_ bv0 8)) (concat (_ bv0 24) (select packet (_ bv30 32))))))
(assert (not (= (concat (_ bv0 24) (select packet (_ bv242 32))) (_ bv1 32))))
(assert (= (concat (_ bv0 24) (select packet (_ bv242 32))) (_ bv3 32)))
(assert (let ((?v_0 (bvadd (_ bv242 32) (concat (_ bv0 24) (select packet (_ bv241 32)))))) (not (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv547 32))))))
(check-sat)
(exit)
